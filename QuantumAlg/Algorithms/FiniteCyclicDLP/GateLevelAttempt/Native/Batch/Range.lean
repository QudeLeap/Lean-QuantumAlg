/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Batch.Reuse

/-!
# Joint original Born law of actual successive finite-cyclic samples

The chronological loop writes distinct retained finite samples on the same
bank. Its joint law follows by composing the actual conditional law and the
proved separation of all earlier sample cells. Arbitrary weights of disjoint
structural reads and every reference matrix entry remain in the equation.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt.Native.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G]
  (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (P : KnownOrderProblem G) (count : Nat)

/-- A joint event observes the real finite cells in the selected chronological positions. -/
def terminalIndicator (length : Nat) (indices : Fin length → Fin count)
    (outcomes : Fin length → Fin (sampleWidth P) → Bool)
    (store : Store (context base noQuantum P count)) : ℂ :=
  ∏ index : Fin length,
    if observedOutcome P (store.read (samples base noQuantum P count (indices index))) =
      outcomes index then 1 else 0

private theorem reference_congr {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum P count) Reference History)
    (first second : Store (context base noQuantum P count) → ℂ)
    (equal : ∀ store, first store = second store) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum state (fun entry _ => first entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => second entry.1) leftRef rightRef :=
  congrArg (fun observe : Store (context base noQuantum P count) → ℂ =>
    ExecutionState.referenceFiberSum state (fun entry _ => observe entry.1) leftRef rightRef)
      (funext equal)

/-- Every actual reset-and-sample stage contributes its original independent Born factor. -/
theorem nativeFiniteCyclicBatch_range_reference
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    ∀ (length : Nat) (indices : Fin length → Fin count) (_distinct : Function.Injective indices)
      {shape : CShape} (input : CInputRef (context base noQuantum P count) shape)
      (_separate : ∀ index position,
        (cells base noQuantum P count (indices index) position).key ∉ input.storageKeys)
      {Reference : Register} {History : Type} [Fintype History]
      (state : State (context base noQuantum P count) Reference History)
      (weight : shape.Value → ℂ) (outcomes : Fin length → Fin (sampleWidth P) → Bool)
      (leftRef rightRef : Reference.Index),
      ExecutionState.referenceFiberSum
        ((Circuit.forRange length (fun index =>
          reusedSample base noQuantum P count B ux (indices index))).execute Reference state)
        (fun entry _ => weight (entry.1.read input) *
          terminalIndicator base noQuantum P count length indices outcomes entry.1)
        leftRef rightRef =
      (∏ index : Fin length, ((outcomePMF P B ux (outcomes index)).toReal : ℂ)) *
        ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read input))
          leftRef rightRef := by
  intro length
  induction length with
  | zero =>
      intro indices _distinct shape input _separate Reference History _
        state weight outcomes leftRef rightRef
      have executed := congrArg
        (fun output : State (context base noQuantum P count) Reference (History × Unit) =>
          ExecutionState.referenceFiberSum output
            (fun entry _ => weight (entry.1.read input)) leftRef rightRef)
        (Circuit.execute_id_mapClassical Reference state)
      have transported := executed.trans (ExecutionState.referenceFiberSum_mapClassical
        state (fun entry => (entry.1, (entry.2, ()))) _ leftRef rightRef)
      simp only [terminalIndicator, Fin.prod_univ_zero, mul_one, one_mul]
      exact transported
  | succ length ih =>
      intro indices distinct shape input separate Reference History _
        state weight outcomes leftRef rightRef
      let joint : CInputRef (context base noQuantum P count)
          (.product shape (.fixedVector (sampleWidth P) (.finite 2))) :=
        .product input (samples base noQuantum P count (indices 0))
      let first := reusedSample base noQuantum P count B ux (indices 0)
      let rest := Circuit.forRange length fun index =>
        reusedSample base noQuantum P count B ux (indices index.succ)
      let advanced := first.execute Reference state
      let headIndicator := fun value : (CShape.fixedVector (sampleWidth P) (.finite 2)).Value =>
        if observedOutcome P value = outcomes 0 then (1 : ℂ) else 0
      let tailWeight := fun value :
          (CShape.product shape (.fixedVector (sampleWidth P) (.finite 2))).Value =>
        weight value.first * headIndicator value.second
      have tailDistinct : Function.Injective (fun index : Fin length => indices index.succ) :=
        fun _ _ same => Fin.succ_injective _ (distinct same)
      have tailSeparate : ∀ (index : Fin length) position,
          (cells base noQuantum P count (indices index.succ) position).key ∉
            joint.storageKeys := by
        intro index position present
        rcases List.mem_append.mp present with original | head
        · exact separate index.succ position original
        · apply nativeFiniteCyclicBatch_cell_not_mem_samples base noQuantum P count
            (indices index.succ) (indices 0) _ position head
          intro same
          have impossible := congrArg Fin.val (distinct same)
          simp only [Fin.val_succ, Fin.val_zero] at impossible
          omega
      have tailLaw := ih (fun index => indices index.succ) tailDistinct joint
        tailSeparate advanced tailWeight (fun index => outcomes index.succ) leftRef rightRef
      let finalWeight := fun store : Store (context base noQuantum P count) =>
        weight (store.read input) *
          terminalIndicator base noQuantum P count (length + 1) indices outcomes store
      have aligned := reference_congr base noQuantum P count (rest.execute Reference advanced)
        finalWeight (fun store => tailWeight (store.read joint) *
          terminalIndicator base noQuantum P count length
            (fun index => indices index.succ) (fun index => outcomes index.succ) store)
        (fun store => by
          change weight _ * terminalIndicator base noQuantum P count (length + 1)
            indices outcomes store =
            (weight _ * headIndicator (store.read (samples base noQuantum P count (indices 0)))) *
              terminalIndicator base noQuantum P count length
                (fun index => indices index.succ) (fun index => outcomes index.succ) store
          rw [terminalIndicator, Fin.prod_univ_succ]
          exact (mul_assoc _ _ _).symm) leftRef rightRef
      have firstLaw := nativeFiniteCyclicBatch_reusedSample_outcome_reference
        base noQuantum P count ux (indices 0) B input (separate 0)
        state weight (outcomes 0) leftRef rightRef
      have sequence := Circuit.referenceFiberSum_execute_seq first rest state finalWeight
        leftRef rightRef
      refine sequence.trans (aligned.trans (tailLaw.trans ?_))
      change (∏ index : Fin length,
        ((outcomePMF P B ux (outcomes index.succ)).toReal : ℂ)) *
          ExecutionState.referenceFiberSum (first.execute Reference state)
            (fun entry _ => weight (entry.1.read input) *
              if observedOutcome P
                (entry.1.read (samples base noQuantum P count (indices 0))) = outcomes 0
              then 1 else 0) leftRef rightRef = _
      rw [firstLaw, Fin.prod_univ_succ]
      ring

end

end QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt.Native.Batch
