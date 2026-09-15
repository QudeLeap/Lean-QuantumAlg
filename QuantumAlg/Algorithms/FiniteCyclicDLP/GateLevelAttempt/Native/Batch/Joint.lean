/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Batch.Range

/-!
# The original joint law of the complete allocated finite-cyclic batch

The first sample uses the original preparation, and every subsequent sample
pays for resetting the same bank. The actual allocator establishes the seed
and protects each incoming operand. The resulting joint law includes zero
samples and retains every reference coefficient of the original input.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt.Native.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G]
  (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (P : KnownOrderProblem G) (count : Nat)

/-- The first real sample and all paid successors have the original joint Born law. -/
theorem nativeFiniteCyclicBatch_sampleBatch_reference
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    {shape : CShape} (input : CInputRef (context base noQuantum P count) shape)
    (separate : ∀ slot position,
      (cells base noQuantum P count slot position).key ∉ input.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum P count) Reference History)
    (seeded : BasisSeeded.Holds (resetLabel base noQuantum P count ux) state)
    (weight : shape.Value → ℂ) (outcomes : Fin count → Fin (sampleWidth P) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((sampleBatch base noQuantum P B ux count).execute Reference state)
      (fun entry _ => weight (entry.1.read input) *
        terminalIndicator base noQuantum P count count id outcomes entry.1) leftRef rightRef =
    (∏ index : Fin count, ((outcomePMF P B ux (outcomes index)).toReal : ℂ)) *
      ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read input))
        leftRef rightRef := by
  cases count with
  | zero =>
      have executed := congrArg
        (fun output : State (context base noQuantum P 0) Reference (History × Unit) =>
          ExecutionState.referenceFiberSum output
            (fun entry _ => weight (entry.1.read input)) leftRef rightRef)
        (Circuit.execute_id_mapClassical Reference state)
      have transported := executed.trans (ExecutionState.referenceFiberSum_mapClassical
        state (fun entry => (entry.1, (entry.2, ()))) _ leftRef rightRef)
      simp only [sampleBatch, terminalIndicator, Fin.prod_univ_zero, mul_one, one_mul]
      exact transported
  | succ length =>
      let joint : CInputRef (context base noQuantum P (length + 1))
          (.product shape (.fixedVector (sampleWidth P) (.finite 2))) :=
        .product input (samples base noQuantum P (length + 1) 0)
      let first := sample base noQuantum P (length + 1) B ux 0
      let rest := Circuit.forRange length fun index =>
        reusedSample base noQuantum P (length + 1) B ux index.succ
      let advanced := first.execute Reference state
      let headIndicator := fun value : (CShape.fixedVector (sampleWidth P) (.finite 2)).Value =>
        if observedOutcome P value = outcomes 0 then (1 : ℂ) else 0
      let tailWeight := fun value :
          (CShape.product shape (.fixedVector (sampleWidth P) (.finite 2))).Value =>
        weight value.first * headIndicator value.second
      have tailSeparate : ∀ (index : Fin length) position,
          (cells base noQuantum P (length + 1) index.succ position).key ∉
            joint.storageKeys := by
        intro index position present
        rcases List.mem_append.mp present with original | head
        · exact separate index.succ position original
        · apply nativeFiniteCyclicBatch_cell_not_mem_samples base noQuantum P (length + 1)
            index.succ 0 _ position head
          intro same
          have impossible := congrArg Fin.val same
          simp only [Fin.val_succ, Fin.val_zero] at impossible
          omega
      have tailLaw := nativeFiniteCyclicBatch_range_reference base noQuantum P (length + 1)
        B ux length Fin.succ (Fin.succ_injective _) joint tailSeparate advanced tailWeight
        (fun index => outcomes index.succ) leftRef rightRef
      let finalWeight := fun store : Store (context base noQuantum P (length + 1)) =>
        weight (store.read input) *
          terminalIndicator base noQuantum P (length + 1) (length + 1) id outcomes store
      have aligned := reference_congr base noQuantum P (length + 1)
        (rest.execute Reference advanced) finalWeight (fun store =>
          tailWeight (store.read joint) * terminalIndicator base noQuantum P (length + 1)
            length Fin.succ (fun index => outcomes index.succ) store) (fun store => by
          change weight _ * terminalIndicator base noQuantum P (length + 1) (length + 1)
            id outcomes store =
            (weight _ * headIndicator (store.read (samples base noQuantum P (length + 1) 0))) *
              terminalIndicator base noQuantum P (length + 1) length Fin.succ
                (fun index => outcomes index.succ) store
          rw [terminalIndicator, Fin.prod_univ_succ]
          exact (mul_assoc _ _ _).symm) leftRef rightRef
      have firstLaw := nativeFiniteCyclicBatch_sample_outcome_reference
        base noQuantum P (length + 1) B ux 0 input (separate 0)
        state seeded weight (outcomes 0) leftRef rightRef
      have sequence := Circuit.referenceFiberSum_execute_seq first rest state finalWeight
        leftRef rightRef
      refine sequence.trans (aligned.trans (tailLaw.trans ?_))
      change (∏ index : Fin length,
        ((outcomePMF P B ux (outcomes index.succ)).toReal : ℂ)) *
          ExecutionState.referenceFiberSum (first.execute Reference state)
            (fun entry _ => weight (entry.1.read input) *
              if observedOutcome P
                (entry.1.read (samples base noQuantum P (length + 1) 0)) = outcomes 0
              then 1 else 0) leftRef rightRef = _
      rw [firstLaw, Fin.prod_univ_succ]
      ring

/-- Actual allocation establishes the seed and yields the original complete batch law. -/
theorem nativeFiniteCyclicBatch_code_reference
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    {shape : CShape} (input : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) (weight : shape.Value → ℂ)
    (outcomes : Fin count → Fin (sampleWidth P) → Bool) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((code base noQuantum P count B ux).execute Reference state)
      (fun entry _ => weight (entry.1.read (liftInput base noQuantum P count input)) *
        terminalIndicator base noQuantum P count count id outcomes entry.1) leftRef rightRef =
    (∏ index : Fin count, ((outcomePMF P B ux (outcomes index)).toReal : ℂ)) *
      ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read input))
        leftRef rightRef := by
  have sequence := Circuit.referenceFiberSum_execute_seq (allocate base noQuantum P count ux)
    (sampleBatch base noQuantum P B ux count) state
    (fun store => weight (store.read (liftInput base noQuantum P count input)) *
      terminalIndicator base noQuantum P count count id outcomes store) leftRef rightRef
  have samples := nativeFiniteCyclicBatch_sampleBatch_reference base noQuantum P count B ux
    (liftInput base noQuantum P count input)
    (nativeFiniteCyclicBatch_cell_not_mem_liftInput base noQuantum P count input)
    ((allocate base noQuantum P count ux).execute Reference state)
    (nativeFiniteCyclicBatch_allocate_seeded base noQuantum P count ux state)
    weight outcomes leftRef rightRef
  exact sequence.trans (samples.trans (congrArg (fun coefficient : ℂ =>
    (∏ index : Fin count, ((outcomePMF P B ux (outcomes index)).toReal : ℂ)) * coefficient)
      (nativeFiniteCyclicBatch_allocate_reference base noQuantum P count ux input state
        weight leftRef rightRef)))

end

end QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt.Native.Batch
