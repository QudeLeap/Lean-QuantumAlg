/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Recovery.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Reuse.Resources

/-!
# Native event and depth budgets for the actual finite batch chain

The first actual batch is charged once. Each subsequent batch contributes
its existing complete same-bank sampling and recovery envelope, including
all measured rounds and their actual reset work. The number of later batches
is explicit, and every claimed bound applies to one path of the same code.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetryChain

noncomputable section

open Execution ShortDLP.CompiledMAU

attribute [local irreducible] NativeBatchRecovery.context NativeBatchReuseRecovery.context

/-- Independent native-coordinate allowance for exactly the requested later batches. -/
def suffixEventEnvelope (N count : Nat) : ResourcePool RuntimeRound.model :=
  count • NativeBatchReuseRecovery.eventEnvelope N

/-- Independent serial allowance for the actual later sampled and recovered batches. -/
def suffixDepthBound (N count : Nat) : Nat := count * NativeBatchReuseRecovery.depthBound N

/-- The first batch is paid once before the actual repeated continuation. -/
def eventEnvelope (N count : Nat) : ResourcePool RuntimeRound.model :=
  NativeBatchRecovery.eventEnvelope N + suffixEventEnvelope N count

/-- The first batch precedes all actual later-batch dependencies. -/
def depthBound (N count : Nat) : Nat :=
  NativeBatchRecovery.depthBound N + suffixDepthBound N count

private lemma sequence_pool {pre middle post : RuntimeCtx .quantum}
    (first : Circuit RuntimeRound.model pre middle)
    (second : Circuit RuntimeRound.model middle post)
    (path : (Circuit.seq first second).Path) :
    (Circuit.seq first second).resourcePool path =
      first.resourcePool path.1 + second.resourcePool path.2 :=
  ResourcePool.ofList_append _ _

variable {N : Nat}

/-- Every actual continuation path obeys the independent number-of-batches event formula. -/
lemma suffixCode_pool_le (input : Input N) (start : RuntimeCtx .quantum)
    (wires : start.quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
    (originalCells : Fin (measurementBits N) → CWriteRef start (.finite 2))
    (count : Nat) (path : (suffixCode input start wires originalCells count).Path) :
    (suffixCode input start wires originalCells count).resourcePool path ≤
      suffixEventEnvelope N count := by
  induction count generalizing start with
  | zero => exact le_rfl
  | succ count induction =>
      have first := NativeBatchReuseRecovery.code_pool_le start wires originalCells input path.1
      have later := induction (NativeBatchReuseRecovery.context start N)
        ((NativeBatchReuseRecovery.context_base_wires start N).trans wires)
        (fun index => reuseWrite N (originalCells index)) path.2
      have combined := add_le_add first later
      have actual := sequence_pool
        (NativeBatchReuseRecovery.code start wires originalCells input)
        (suffixCode input (NativeBatchReuseRecovery.context start N)
          ((NativeBatchReuseRecovery.context_base_wires start N).trans wires)
          (fun index => reuseWrite N (originalCells index)) count) path
      refine actual.le.trans ?_
      simpa only [suffixEventEnvelope, succ_nsmul, add_comm] using combined

/-- The same actual continuation path obeys the independent serial depth formula. -/
lemma suffixCode_depth_le (input : Input N) (start : RuntimeCtx .quantum)
    (wires : start.quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
    (originalCells : Fin (measurementBits N) → CWriteRef start (.finite 2))
    (count : Nat) (path : (suffixCode input start wires originalCells count).Path) :
    (suffixCode input start wires originalCells count).depth (fun _ => 1) path ≤
      suffixDepthBound N count := by
  induction count generalizing start with
  | zero =>
      have budget : suffixDepthBound N 0 = 0 := Nat.zero_mul _
      rw [budget]
      exact Nat.le_refl 0
  | succ count induction =>
      have first := NativeBatchReuseRecovery.code_depth_le start wires originalCells input path.1
      have later := induction (NativeBatchReuseRecovery.context start N)
        ((NativeBatchReuseRecovery.context_base_wires start N).trans wires)
        (fun index => reuseWrite N (originalCells index)) path.2
      have combined := Nat.add_le_add first later
      have actual := Circuit.depth_seq
        (NativeBatchReuseRecovery.code start wires originalCells input)
        (suffixCode input (NativeBatchReuseRecovery.context start N)
          ((NativeBatchReuseRecovery.context_base_wires start N).trans wires)
          (fun index => reuseWrite N (originalCells index)) count) (fun _ => 1) path.1 path.2
      refine actual.le.trans ?_
      simpa only [suffixDepthBound, Nat.succ_mul, Nat.add_comm] using combined

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- One first-batch execution and its actual repeated suffix meet every native coordinate. -/
lemma code_pool_le (input : Input N) (count : Nat)
    (path : (code base noQuantum input count).Path) :
    (code base noQuantum input count).resourcePool path ≤ eventEnvelope N count :=
  (sequence_pool (NativeBatchRecovery.code base noQuantum input)
    (suffixCode input (NativeBatchRecovery.context base noQuantum N)
      (firstWires base noQuantum N) (firstCells base noQuantum N) count) path).le.trans
    (add_le_add (NativeBatchRecovery.code_pool_le base noQuantum input path.1)
      (suffixCode_pool_le input (NativeBatchRecovery.context base noQuantum N)
        (firstWires base noQuantum N) (firstCells base noQuantum N) count path.2))

/-- The independent native ledger also bounds the number of operations on this same path. -/
lemma code_eventCount_le (input : Input N) (count : Nat)
    (path : (code base noQuantum input count).Path) :
    ((code base noQuantum input count).eventTrace path).length ≤ (eventEnvelope N count).card :=
  Multiset.card_le_card (code_pool_le base noQuantum input count path)

/-- The full serial dependency includes the first batch followed by every later batch. -/
lemma code_depth_le (input : Input N) (count : Nat)
    (path : (code base noQuantum input count).Path) :
    (code base noQuantum input count).depth (fun _ => 1) path ≤ depthBound N count :=
  Nat.add_le_add (NativeBatchRecovery.code_depth_le base noQuantum input path.1)
    (suffixCode_depth_le input (NativeBatchRecovery.context base noQuantum N)
      (firstWires base noQuantum N) (firstCells base noQuantum N) count path.2)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetryChain
