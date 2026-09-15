/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Batch.Probability
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.Observation

/-!
# Original conditional sampling law after paid reuse of the finite-cyclic bank

The actual preparation supplies the first seed. Each later round establishes
that same seed by measuring and correcting every live wire, while preserving
all disjoint structural reads jointly with the external reference. Thus
the original conditional Born law holds on arbitrary incoming states without
requiring callers to promise a clean bank or initialized measurement cells.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical
namespace GateLevelAttempt.Native.Batch

open Execution

noncomputable section

universe u

variable {G : Type u} [Group G]
  (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (P : KnownOrderProblem G) (count : Nat) (ux : UxAccess P) (slot : Fin count)

/-- Actual reset preserves each incoming structural operand's full reference weight. -/
theorem nativeFiniteCyclicBatch_reset_reference {shape : CShape} (input : CInputRef (context base
  noQuantum P count) shape)
    (separate : ∀ index : Fin (sampleWidth P),
      (cells base noQuantum P count slot index).key ∉ input.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum P count) Reference History) (weight : shape.Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((reset base noQuantum P count ux slot).execute Reference
      state)
        (fun entry _ => weight (entry.1.read input)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read input)) left right := by
  have unchanged : ∀ (wire : Fin (context base noQuantum P count).systemCount)
      (store : Store (context base noQuantum P count)) result,
      weight ((store.write (resetCell base noQuantum P count slot wire) result).read
        input) =
      weight (store.read input) := by
    intro wire store result
    apply congrArg weight
    apply Store.read_write_of_not_mem_storageKeys
    rw [nativeFiniteCyclicBatch_resetCell_key]
    exact separate _
  exact QuditShift.resetToBasis_weighted_reference (resetCell base noQuantum P count slot)
    (resetLabel base noQuantum P count ux) state
    (fun store => weight (store.read input)) unchanged left right

/-- Every later actual round has the same original law after its own paid reset. -/
theorem nativeFiniteCyclicBatch_reusedSample_outcome_reference
    (B : UniformSuperposition.BinaryExpansion P.order)
    {shape : CShape} (input : CInputRef (context base noQuantum P count) shape)
    (separate : ∀ index : Fin (sampleWidth P),
      (cells base noQuantum P count slot index).key ∉ input.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum P count) Reference History) (weight : shape.Value → ℂ)
    (outcome : Fin (sampleWidth P) → Bool) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((reusedSample base noQuantum P count B ux slot).execute Reference state)
        (fun entry _ => weight (entry.1.read input) *
          if observedOutcome P (entry.1.read (samples base noQuantum P count slot)) = outcome
          then 1 else 0) left right =
      ((outcomePMF P B ux outcome).toReal : ℂ) * ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read input)) left right := by
  classical
  have first := Circuit.referenceFiberSum_execute_seq (reset base noQuantum P count ux slot)
    (sample base noQuantum P count B ux slot) state
    (fun store => weight (store.read input) *
      if observedOutcome P (store.read (samples base noQuantum P count slot)) = outcome
      then (1 : ℂ) else 0) left right
  have born := nativeFiniteCyclicBatch_sample_outcome_reference base noQuantum P count B ux slot
    input separate
    ((reset base noQuantum P count ux slot).execute Reference state)
    (nativeFiniteCyclicBatch_reset_seeded base noQuantum P count ux slot state) weight outcome left
      right
  exact first.trans (born.trans (congrArg
    (fun coefficient : ℂ => ((outcomePMF P B ux outcome).toReal : ℂ) * coefficient)
    (nativeFiniteCyclicBatch_reset_reference base noQuantum P count ux slot input separate state
      weight left right)))

end

end GateLevelAttempt.Native.Batch
end QuantumAlg.FiniteCyclicDLP.Canonical
