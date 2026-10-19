/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Recovery.Space
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Reuse.Space
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Exact retained capacity and actual peaks of the finite same-bank batch chain

Only persistent classical source, outcome and factor cells accumulate with
later batches. Their exact final capacity is separated from the temporary
sampler and recovery workspace. Sequential peaks take a maximum, so the
quantum bank and native-power scratch are not multiplied by the batch count.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetryChain

noncomputable section

open Execution ShortDLP.CompiledMAU

/-- Exact persistent capacity after the sole first batch and all subsequent batches. -/
def retainedSpace (N count : Nat) : SpacePool .quantum :=
  NativeBatchRecovery.retainedSpace N + count • NativeBatchReuseRecovery.retainedSpace N

/-- Later batches accumulate only retained cells beside one temporary execution allowance. -/
def suffixAllowance (N count : Nat) : SpacePool .quantum :=
  count • NativeBatchReuseRecovery.retainedSpace N + NativeBatchReuseRecovery.additionalSpace N

/-- The complete peak is the maximum of the first-batch and subsequent-batch allowances. -/
def additionalSpace (N count : Nat) : SpacePool .quantum :=
  SpacePool.max (NativeBatchRecovery.additionalSpace N)
    (NativeBatchRecovery.retainedSpace N + suffixAllowance N count)

/-- Every suffix retains exactly the permanent additions of its actual later batches. -/
lemma suffixContext_resident (N count : Nat) (start : RuntimeCtx .quantum) :
    (suffixContext N start count).residentSpace =
      start.residentSpace + count • NativeBatchReuseRecovery.retainedSpace N := by
  induction count generalizing start with
  | zero => simp only [suffixContext, zero_nsmul, add_zero]
  | succ count induction =>
      change (suffixContext N (NativeBatchReuseRecovery.context start N) count).residentSpace = _
      rw [induction, NativeBatchReuseRecovery.reuseRecovery_context_resident, succ_nsmul]
      ac_rfl

/-- Every persistent later-batch cell remains an owned auxiliary of exactly the same capacity. -/
lemma suffixContext_auxiliary (N count : Nat) (start : RuntimeCtx .quantum) :
    (suffixContext N start count).auxiliarySpace =
      start.auxiliarySpace + count • NativeBatchReuseRecovery.retainedSpace N := by
  induction count generalizing start with
  | zero => simp only [suffixContext, zero_nsmul, add_zero]
  | succ count induction =>
      change (suffixContext N (NativeBatchReuseRecovery.context start N) count).auxiliarySpace = _
      rw [induction, NativeBatchReuseRecovery.reuseRecovery_context_auxiliary, succ_nsmul]
      ac_rfl

/-- Repeating a batch adds no permanent quantum capacity in any native dimension. -/
lemma retainedSpace_quantum (N count : Nat) (dimension : ℕ+) :
    retainedSpace N count (.quantumSystems dimension) =
      NativeBatchRecovery.retainedSpace N (.quantumSystems dimension) := by
  simp only [retainedSpace, Pi.add_apply, Pi.smul_apply,
    NativeBatchReuseRecovery.retainedSpace_quantum, smul_zero, Nat.add_zero]

/-- The entire quantum peak allowance is independent of the number of subsequent batches. -/
lemma additionalSpace_quantum (N count : Nat) (dimension : ℕ+) :
    additionalSpace N count (.quantumSystems dimension) =
      additionalSpace N 0 (.quantumSystems dimension) := by
  simp only [additionalSpace, suffixAllowance, SpacePool.max, Pi.add_apply, Pi.smul_apply,
    NativeBatchReuseRecovery.retainedSpace_quantum, smul_zero, Nat.zero_add]

private lemma temporary_le_suffix (retained temporary : SpacePool .quantum) (count : Nat) :
    temporary ≤ count • retained + temporary :=
  fun _ => Nat.le_add_left _ _

private lemma successorAllowance (original retained temporary : SpacePool .quantum)
    (count : Nat) :
    (original + retained) + (count • retained + temporary) =
      original + ((count + 1) • retained + temporary) := by
  rw [succ_nsmul]
  ac_rfl

variable {N : Nat}

/-- Every actual suffix resident peak includes accumulated retained cells and one scratch peak. -/
lemma suffix_resident_le (input : Input N) :
    ∀ (count : Nat) (start : RuntimeCtx .quantum)
      (wires : start.quantumWires =
        (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
      (originalCells : Fin (measurementBits N) → CWriteRef start (.finite 2))
      (path : (suffixCode input start wires originalCells count).Path),
      (suffixCode input start wires originalCells count).peakResidentSpace path ≤
        start.residentSpace + suffixAllowance N count := by
  intro count
  induction count with
  | zero =>
      intro start wires originalCells path
      change SpacePool.max start.residentSpace 0 ≤ start.residentSpace + suffixAllowance N 0
      rw [SpacePool.max_zero]
      exact fun _ => Nat.le_add_right _ _
  | succ count induction =>
      intro start wires originalCells path
      refine (Circuit.peakResidentSpace_seq
        (NativeBatchReuseRecovery.code start wires originalCells input)
        (suffixCode input (NativeBatchReuseRecovery.context start N)
          ((NativeBatchReuseRecovery.context_base_wires start N).trans wires)
          (fun index => reuseWrite N (originalCells index)) count) path).le.trans ?_
      apply SpacePool.max_le
      · exact (NativeBatchReuseRecovery.code_resident_le
          start wires originalCells input path.1).trans
            (add_le_add (le_refl _) (temporary_le_suffix _ _ (count + 1)))
      · have bound := induction (NativeBatchReuseRecovery.context start N)
          ((NativeBatchReuseRecovery.context_base_wires start N).trans wires)
          (fun index => reuseWrite N (originalCells index)) path.2
        rw [NativeBatchReuseRecovery.reuseRecovery_context_resident] at bound
        exact bound.trans_eq (successorAllowance _ _ _ count)

/-- The same actual suffix charges retained ownership and one auxiliary scratch peak. -/
lemma suffix_auxiliary_le (input : Input N) :
    ∀ (count : Nat) (start : RuntimeCtx .quantum)
      (wires : start.quantumWires =
        (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
      (originalCells : Fin (measurementBits N) → CWriteRef start (.finite 2))
      (path : (suffixCode input start wires originalCells count).Path),
      (suffixCode input start wires originalCells count).peakAuxiliarySpace path ≤
        start.auxiliarySpace + suffixAllowance N count := by
  intro count
  induction count with
  | zero =>
      intro start wires originalCells path
      change SpacePool.max start.auxiliarySpace 0 ≤ start.auxiliarySpace + suffixAllowance N 0
      rw [SpacePool.max_zero]
      exact fun _ => Nat.le_add_right _ _
  | succ count induction =>
      intro start wires originalCells path
      refine (Circuit.peakAuxiliarySpace_seq
        (NativeBatchReuseRecovery.code start wires originalCells input)
        (suffixCode input (NativeBatchReuseRecovery.context start N)
          ((NativeBatchReuseRecovery.context_base_wires start N).trans wires)
          (fun index => reuseWrite N (originalCells index)) count) path).le.trans ?_
      apply SpacePool.max_le
      · exact (NativeBatchReuseRecovery.code_auxiliary_le
          start wires originalCells input path.1).trans
            (add_le_add (le_refl _) (temporary_le_suffix _ _ (count + 1)))
      · have bound := induction (NativeBatchReuseRecovery.context start N)
          ((NativeBatchReuseRecovery.context_base_wires start N).trans wires)
          (fun index => reuseWrite N (originalCells index)) path.2
        rw [NativeBatchReuseRecovery.reuseRecovery_context_auxiliary] at bound
        exact bound.trans_eq (successorAllowance _ _ _ count)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- The final context contains exactly the original caller and all actually retained capacity. -/
lemma context_resident (N count : Nat) :
    (context base noQuantum N count).residentSpace =
      base.residentSpace + retainedSpace N count := by
  unfold context
  rw [suffixContext_resident, NativeBatchRecovery.firstRecovery_context_resident]
  exact add_assoc _ _ _

/-- The final owned auxiliary capacity has exactly the same retained additions. -/
lemma context_auxiliary (N count : Nat) :
    (context base noQuantum N count).auxiliarySpace =
      base.auxiliarySpace + retainedSpace N count := by
  unfold context
  rw [suffixContext_auxiliary, NativeBatchRecovery.firstRecovery_context_auxiliary]
  exact add_assoc _ _ _

/-- Resident capacity takes the maximum of the actual first execution and its same-bank suffix. -/
lemma code_resident_le (input : Input N) (count : Nat)
    (path : (code base noQuantum input count).Path) :
    (code base noQuantum input count).peakResidentSpace path ≤
      base.residentSpace + additionalSpace N count := by
  refine (Circuit.peakResidentSpace_seq (NativeBatchRecovery.code base noQuantum input)
    (suffixCode input (NativeBatchRecovery.context base noQuantum N)
      (firstWires base noQuantum N) (firstCells base noQuantum N) count) path).le.trans ?_
  apply SpacePool.max_le
  · exact (NativeBatchRecovery.code_resident_le base noQuantum input path.1).trans
      (add_le_add (le_refl _) (SpacePool.le_max_left _ _))
  · have bound := suffix_resident_le input count
      (NativeBatchRecovery.context base noQuantum N) (firstWires base noQuantum N)
      (firstCells base noQuantum N) path.2
    rw [NativeBatchRecovery.firstRecovery_context_resident, add_assoc] at bound
    exact bound.trans (add_le_add (le_refl _) (SpacePool.le_max_right _ _))

/-- Auxiliary capacity charges permanent results and temporary native-power storage only once. -/
lemma code_auxiliary_le (input : Input N) (count : Nat)
    (path : (code base noQuantum input count).Path) :
    (code base noQuantum input count).peakAuxiliarySpace path ≤
      base.auxiliarySpace + additionalSpace N count := by
  refine (Circuit.peakAuxiliarySpace_seq (NativeBatchRecovery.code base noQuantum input)
    (suffixCode input (NativeBatchRecovery.context base noQuantum N)
      (firstWires base noQuantum N) (firstCells base noQuantum N) count) path).le.trans ?_
  apply SpacePool.max_le
  · exact (NativeBatchRecovery.code_auxiliary_le base noQuantum input path.1).trans
      (add_le_add (le_refl _) (SpacePool.le_max_left _ _))
  · have bound := suffix_auxiliary_le input count
      (NativeBatchRecovery.context base noQuantum N) (firstWires base noQuantum N)
      (firstCells base noQuantum N) path.2
    rw [NativeBatchRecovery.firstRecovery_context_auxiliary, add_assoc] at bound
    exact bound.trans (add_le_add (le_refl _) (SpacePool.le_max_right _ _))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetryChain
