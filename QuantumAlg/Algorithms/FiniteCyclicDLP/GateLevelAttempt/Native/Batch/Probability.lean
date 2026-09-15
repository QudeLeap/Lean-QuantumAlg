/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Batch.Observation

/-!
# Each retained finite-cyclic sample has the original conditional Born law

The real unitary and finite measurement sequence determine every sample
probability. The same equation retains arbitrary complex weights of preserved
structural reads disjoint from the current sample cells and every off-diagonal
reference entry. The low-level seed is established by the actual allocator
or the actual paid reset.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical
namespace GateLevelAttempt.Native.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem indicator_decision {Value : Type} (condition : Prop)
    (first second : Decidable condition) (selected rejected : Value) :
    @ite Value condition first selected rejected =
      @ite Value condition second selected rejected := by
  cases Subsingleton.elim first second
  rfl

private theorem source_weight (amplitude coefficient : ℂ) :
    amplitude * coefficient * star amplitude = ((‖amplitude‖ ^ 2 : ℝ) : ℂ) * coefficient := by
  calc
    _ = (amplitude * star amplitude) * coefficient := by ring
    _ = _ := congrArg (fun value : ℂ => value * coefficient)
      (by simpa only [Complex.star_def, Complex.ofReal_pow] using Complex.mul_conj' amplitude)

private theorem weighted_fiber {Basis : Type} [Fintype Basis]
    (predicate : Basis → Prop) (decision : DecidablePred predicate)
    (value : Basis → ℝ) (coefficient : ℂ) :
    (∑ basis : Basis, (@ite ℂ (predicate basis) (decision basis) 1 0) *
      ((value basis : ℂ) * coefficient)) =
      ((∑ basis : Basis,
        @ite ℝ (predicate basis) (decision basis) (value basis) 0 : ℝ) : ℂ) * coefficient := by
  have terms :
      (∑ basis : Basis, (@ite ℂ (predicate basis) (decision basis) 1 0) *
        ((value basis : ℂ) * coefficient)) =
      ∑ basis : Basis,
        ((@ite ℝ (predicate basis) (decision basis) (value basis) 0) : ℂ) * coefficient := by
    apply Finset.sum_congr rfl
    intro basis _
    by_cases selected : predicate basis
    · simp only [if_pos selected, one_mul]
    · simp only [if_neg selected, zero_mul, Complex.ofReal_zero]
  exact terms.trans ((Finset.sum_mul _ _ _).symm.trans
    (congrArg (fun total : ℂ => total * coefficient)
      (Complex.ofReal_sum (s := Finset.univ)
        (fun basis => @ite ℝ (predicate basis) (decision basis) (value basis) 0)).symm))

universe u

variable {G : Type u} [Group G]
  (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (P : KnownOrderProblem G) (count : Nat)

/-- One actual sample factors its original Born law from every preserved input-Reference weight. -/
theorem nativeFiniteCyclicBatch_sample_outcome_reference
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) (slot : Fin count)
    {shape : CShape} (input : CInputRef (context base noQuantum P count) shape)
    (separate : ∀ index : Fin (sampleWidth P),
      (cells base noQuantum P count slot index).key ∉ input.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum P count) Reference History)
    (seeded : BasisSeeded.Holds (resetLabel base noQuantum P count ux) state)
    (weight : shape.Value → ℂ) (outcome : Fin (sampleWidth P) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((sample base noQuantum P count B ux slot).execute Reference
      state)
      (fun entry _ => weight (entry.1.read input) *
        if observedOutcome P (entry.1.read (samples base noQuantum P count slot)) = outcome then 1
          else 0)
        leftRef rightRef =
      ((outcomePMF P B ux outcome).toReal : ℂ) * ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read input))
        leftRef rightRef := by
  classical
  let observed := fun store : Store (context base noQuantum P count) =>
    weight (store.read input) *
      if observedOutcome P (store.read (samples base noQuantum P count slot)) = outcome then (1 : ℂ)
        else 0
  let unitary := Circuit.unitary (member base noQuantum P count B ux)
    (nativeFiniteCyclicBatch_member_physicalIdx base noQuantum P count B ux)
  have first := Circuit.referenceFiberSum_execute_seq unitary
    (Circuit.measurementSequence (readouts base noQuantum P count slot)) state observed leftRef
      rightRef
  refine first.trans ((Circuit.measurementSequence_referenceFiberSum (readouts base noQuantum P
    count slot)
    (unitary.execute Reference state) (fun entry _ => observed entry.1)
    leftRef rightRef).trans ?_)
  let indicator := fun basis : (context base noQuantum P count).register.Index =>
    if (terminalMeasurement P).readout
      (basisEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count) basis) = outcome
    then (1 : ℂ) else 0
  let oldWeight := fun store : Store (context base noQuantum P count) =>
    weight (store.read input)
  have actualWeight (store : Store (context base noQuantum P count))
      (basis : (context base noQuantum P count).register.Index) :
      observed (Circuit.writeMeasurementPath (readouts base noQuantum P count slot) store
        (Circuit.measurementBasisPath (readouts base noQuantum P count slot) basis)) =
      oldWeight store * indicator basis := by
    dsimp only [observed, oldWeight, indicator]
    rw [nativeFiniteCyclicBatch_measured_input base noQuantum P count slot input separate,
      nativeFiniteCyclicBatch_observed_outcome]
    exact congrArg
      (fun value : ℂ => weight (store.read input) * value)
      (indicator_decision _ _ _ 1 0)
  simp only [actualWeight]
  refine (BasisSeeded.fiber_store_blocks (unitary.execute Reference state)
    (fun store basis => oldWeight store * indicator basis) leftRef rightRef).trans ?_
  rw [Finset.sum_comm]
  have stores :
      (∑ original : Store (context base noQuantum P count),
        ∑ basis : (context base noQuantum P count).register.Index,
          (oldWeight original * indicator basis) *
            ((unitary.execute Reference state).filterClassical
              (fun entry => entry.1 = original)).quantumMarginal.matrix
                (basis, leftRef) (basis, rightRef)) =
      ∑ original : Store (context base noQuantum P count), ((outcomePMF P B ux outcome).toReal : ℂ)
        *
        (oldWeight original *
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            (resetLabel base noQuantum P count ux, leftRef)
            (resetLabel base noQuantum P count ux, rightRef)) := by
    apply Finset.sum_congr rfl
    intro original _
    let coefficient := oldWeight original *
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (resetLabel base noQuantum P count ux, leftRef)
        (resetLabel base noQuantum P count ux, rightRef)
    have terms :
        (∑ basis : (context base noQuantum P count).register.Index,
          (oldWeight original * indicator basis) *
            ((unitary.execute Reference state).filterClassical
              (fun entry => entry.1 = original)).quantumMarginal.matrix
                (basis, leftRef) (basis, rightRef)) =
        ∑ basis : (context base noQuantum P count).register.Index, indicator basis *
          (((‖(evolvedState P B ux).normalized
            (basisEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count) basis)‖ ^ 2
              : ℝ) : ℂ) *
              coefficient) := by
      apply Finset.sum_congr rfl
      intro basis _
      rw [nativeFiniteCyclicBatch_unitary_seed_entry base noQuantum P count ux B state seeded,
        source_weight]
      dsimp only [coefficient]
      ring
    refine terms.trans ((weighted_fiber _ _ _ coefficient).trans ?_)
    apply congrArg (fun probability : ℝ => (probability : ℂ) * coefficient)
    refine ((basisEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count)).sum_comp
      (fun basis => if (terminalMeasurement P).readout basis = outcome then
        ‖(evolvedState P B ux).normalized basis‖ ^ 2 else 0)).trans ?_
    refine Eq.trans ?_
      (TerminalZMeasure.outcomePMF_toReal (terminalMeasurement P) (evolvedState P B ux)
        outcome).symm
    apply Finset.sum_congr rfl
    intro basis _
    exact indicator_decision _ _ _ _ _
  refine stores.trans ?_
  rw [← Finset.mul_sum]
  exact congrArg (fun coefficient : ℂ => ((outcomePMF P B ux outcome).toReal : ℂ) * coefficient)
    (BasisSeeded.referenceFiberSum_seed _ state seeded oldWeight leftRef rightRef).symm

end

end GateLevelAttempt.Native.Batch
end QuantumAlg.FiniteCyclicDLP.Canonical
