/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Recovery.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Reuse.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Layout.Separation
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Results.Laws

/-!
# Live layouts for one first batch and finitely many batches on the same bank

The first batch supplies the sole owned bank and original finite measurement
cells. Every subsequent batch adds only its real source, outcome and factor
cells. Existing writable references are lifted structurally; their keys and
roles do not change. Chronological factor references observe the individual
retained cells without allocating or computing a physical result array.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetryChain

noncomputable section

open Execution ShortDLP.CompiledMAU

/-- An old writable cell crosses a later batch's source, outcomes and retained factor. -/
def reuseWrite (N : Nat) {start : RuntimeCtx .quantum} {shape : CShape}
    (ref : CWriteRef start shape) :
    CWriteRef (NativeBatchReuseRecovery.context start N) shape :=
  (RuntimeResults.liftWrite (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (NativeBatchReuse.sampledWrite start N ref) 16).underRetained
      (NativeBatchReuseRecovery.resultKey start N) (LatticeBatchRecoveryOutput.OutputShape N)
      (NativeBatchReuse.context start N).canonicalFreshKey_fresh

/-- Lifting through a complete later batch keeps exactly the existing storage identity. -/
theorem reuseWrite_key (N : Nat) {start : RuntimeCtx .quantum} {shape : CShape}
    (ref : CWriteRef start shape) : (reuseWrite N ref).key = ref.key :=
  by
    unfold reuseWrite
    dsimp only [CWriteRef.underRetained, CStorageRef.underRetained]
    exact RuntimeResults.shortDLP_runtimeResults_liftWrite_key
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (NativeBatchReuse.sampledWrite start N ref) 16

private theorem resultWrite_role (m ell width : Nat) {shape : CShape}
    {ctx : RuntimeCtx .quantum} (ref : CWriteRef ctx shape) (count : Nat) :
    (RuntimeResults.liftWrite m ell width ref count).toCStorageRef.role =
      ref.toCStorageRef.role := by
  induction count generalizing ctx with
  | zero => rfl
  | succ count induction =>
      exact induction (ref.underRetained ctx.canonicalFreshKey
        (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh)

/-- The writable cell keeps its original ownership role through the actual retained layout. -/
theorem reuseWrite_role (N : Nat) {start : RuntimeCtx .quantum} {shape : CShape}
    (ref : CWriteRef start shape) :
    (reuseWrite N ref).toCStorageRef.role = ref.toCStorageRef.role :=
  by
    unfold reuseWrite
    dsimp only [CWriteRef.underRetained, CStorageRef.underRetained]
    exact resultWrite_role (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (NativeBatchReuse.sampledWrite start N ref) 16

/-- A suffix consists only of the successive actual later-batch contexts. -/
def suffixContext (N : Nat) : RuntimeCtx .quantum → Nat → RuntimeCtx .quantum
  | start, 0 => start
  | start, count + 1 => suffixContext N (NativeBatchReuseRecovery.context start N) count

/-- Lift an existing writable cell through every subsequent real batch. -/
def suffixWrite (N : Nat) {shape : CShape} : {start : RuntimeCtx .quantum} →
    CWriteRef start shape → (count : Nat) → CWriteRef (suffixContext N start count) shape
  | _, ref, 0 => ref
  | _, ref, count + 1 => suffixWrite N (reuseWrite N ref) count

/-- Lift an existing structural read through every subsequent real batch. -/
def suffixInput (N : Nat) {shape : CShape} : {start : RuntimeCtx .quantum} →
    CInputRef start shape → (count : Nat) → CInputRef (suffixContext N start count) shape
  | _, ref, 0 => ref
  | start, ref, count + 1 =>
      suffixInput N (NativeBatchReuseRecovery.callerInput start N ref) count

/-- No suffix changes a preexisting writable storage identity. -/
theorem suffixWrite_key (N : Nat) {start : RuntimeCtx .quantum} {shape : CShape}
    (ref : CWriteRef start shape) (count : Nat) :
    (suffixWrite N ref count).key = ref.key := by
  induction count generalizing start with
  | zero => rfl
  | succ count induction => exact (induction (reuseWrite N ref)).trans (reuseWrite_key N ref)

/-- Every later batch preserves the original writable cell's ownership role. -/
theorem suffixWrite_role (N : Nat) {start : RuntimeCtx .quantum} {shape : CShape}
    (ref : CWriteRef start shape) (count : Nat) :
    (suffixWrite N ref count).toCStorageRef.role = ref.toCStorageRef.role := by
  induction count generalizing start with
  | zero => rfl
  | succ count induction => exact (induction (reuseWrite N ref)).trans (reuseWrite_role N ref)

/-- Every suffix retains precisely the starting bank's ordered physical wire identities. -/
theorem suffixWires (N : Nat) (start : RuntimeCtx .quantum) (count : Nat) :
    (suffixContext N start count).quantumWires = start.quantumWires := by
  induction count generalizing start with
  | zero => rfl
  | succ count induction =>
      exact (induction (NativeBatchReuseRecovery.context start N)).trans
        (NativeBatchReuseRecovery.context_base_wires start N)

/-- Each later batch's actual factor cell remains available in chronological order. -/
def suffixResults (N : Nat) : (start : RuntimeCtx .quantum) → (count : Nat) →
    Fin count → CWriteRef (suffixContext N start count) (LatticeBatchRecoveryOutput.OutputShape N)
  | _, 0, index => Fin.elim0 index
  | start, count + 1, index => Fin.cases
      (suffixWrite N (NativeBatchReuseRecovery.resultRef start N) count)
      (suffixResults N (NativeBatchReuseRecovery.context start N) count) index

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The complete live context after one first batch and `count` later batches. -/
def context (count : Nat) : RuntimeCtx .quantum :=
  suffixContext N (NativeBatchRecovery.context base noQuantum N) count

/-- The original finite measurement cells cross the first batch outcomes and recovery result. -/
def firstCells (index : Fin (measurementBits N)) :
    CWriteRef (NativeBatchRecovery.context base noQuantum N) (.finite 2) :=
  (RuntimeResults.liftWrite (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (NativeBatch.cells base noQuantum N index) 16).underRetained
      (NativeBatchRecovery.resultKey base noQuantum N) (LatticeBatchRecoveryOutput.OutputShape N)
      (NativeBatch.context base noQuantum N).canonicalFreshKey_fresh

/-- The same originally allocated measurement cells remain writable after the entire suffix. -/
def cells (count : Nat) (index : Fin (measurementBits N)) :
    CWriteRef (context base noQuantum N count) (.finite 2) :=
  suffixWrite N (firstCells base noQuantum N index) count

/-- Every final measured-cell reference has its original first-allocation identity. -/
theorem cells_key (count : Nat) (index : Fin (measurementBits N)) :
    (cells base noQuantum N count index).key = (NativeBatch.cells base noQuantum N index).key :=
  by
    refine (suffixWrite_key N (firstCells base noQuantum N index) count).trans ?_
    unfold firstCells
    dsimp only [CWriteRef.underRetained, CStorageRef.underRetained]
    exact RuntimeResults.shortDLP_runtimeResults_liftWrite_key
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (NativeBatch.cells base noQuantum N index) 16

/-- Every original measured-cell ownership role survives all later retained allocations. -/
theorem cells_role (count : Nat) (index : Fin (measurementBits N)) :
    (cells base noQuantum N count index).toCStorageRef.role =
      (NativeBatch.cells base noQuantum N index).toCStorageRef.role :=
  by
    refine (suffixWrite_role N (firstCells base noQuantum N index) count).trans ?_
    unfold firstCells
    dsimp only [CWriteRef.underRetained, CStorageRef.underRetained]
    exact resultWrite_role (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (NativeBatch.cells base noQuantum N index) 16

/-- Distinct measured positions continue to refer to distinct original physical cells. -/
theorem cells_distinct (count : Nat) :
    Function.Injective (fun index => (cells base noQuantum N count index).key) := by
  intro left right equal
  apply NativeBatch.nativeBatch_cells_distinct base noQuantum N
  exact (cells_key base noQuantum N count left).symm.trans
    (equal.trans (cells_key base noQuantum N count right))

/-- The first completed batch has exactly the one originally allocated bank. -/
theorem firstWires :
    (NativeBatchRecovery.context base noQuantum N).quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires :=
  (NativeBatchRecovery.context_quantumWires base noQuantum N).trans
    (NativeBatch.nativeBatch_context_wires base noQuantum N)

/-- Every completed chain preserves that same ordered bank, with no subsequent bank allocation. -/
theorem sameWires (count : Nat) :
    (context base noQuantum N count).quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires :=
  (suffixWires N (NativeBatchRecovery.context base noQuantum N) count).trans
    (firstWires base noQuantum N)

/-- Chronological factor references point to the actual retained cell of each executed batch. -/
def resultWrites (count : Nat) : Fin (count + 1) →
    CWriteRef (context base noQuantum N count) (LatticeBatchRecoveryOutput.OutputShape N) :=
  Fin.cases (suffixWrite N (NativeBatchRecovery.resultRef base noQuantum N) count)
    (suffixResults N (NativeBatchRecovery.context base noQuantum N) count)

/-- The final result family consists only of structural reads of those individual live cells. -/
def resultRefs (count : Nat) (index : Fin (count + 1)) :
    CInputRef (context base noQuantum N count) (LatticeBatchRecoveryOutput.OutputShape N) :=
  .storage (resultWrites base noQuantum N count index).toCStorageRef

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetryChain
