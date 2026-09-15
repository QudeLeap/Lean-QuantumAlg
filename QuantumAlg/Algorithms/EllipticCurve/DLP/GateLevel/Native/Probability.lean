/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Observation

/-!
# Actual literal ECDLP sampling has the original terminal Born law

The real unitary and finite measurement sequence determine every sample
probability. The same equation retains arbitrary complex weights of original
structural inputs and every off-diagonal reference entry. The low-level seed
is established by the actual allocator or the actual paid reset.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

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

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}
  (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)

/-- One actual sample factors its original Born law from every incoming operand-Reference weight. -/
theorem nativeECDLP_sample_outcome_reference
    (B : OrderExpansion (problem I).order) (A : Access I)
    {shape : CShape} (input : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum I) Reference History)
    (seeded : BasisSeeded.Holds (resetLabel base noQuantum I) state)
    (weight : shape.Value → ℂ) (outcome : Fin (sampleWidth I) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((sample base noQuantum I B A).execute Reference state)
      (fun entry _ => weight (entry.1.read (liftInput base noQuantum I input)) *
        if observedOutcome I (entry.1.read (sampleInput base noQuantum I)) = outcome then 1 else 0)
        leftRef rightRef =
      ((outcomePMF I B A outcome).toReal : ℂ) * ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read (liftInput base noQuantum I input)))
        leftRef rightRef := by
  classical
  let observed := fun store : Store (context base noQuantum I) =>
    weight (store.read (liftInput base noQuantum I input)) *
      if observedOutcome I (store.read (sampleInput base noQuantum I)) = outcome then (1 : ℂ) else 0
  let unitary := Circuit.unitary (member base noQuantum I B A)
    (nativeECDLP_member_physicalIdx base noQuantum I B A)
  have first := Circuit.referenceFiberSum_execute_seq unitary
    (Circuit.measurementSequence (readouts base noQuantum I)) state observed leftRef rightRef
  refine first.trans ((Circuit.measurementSequence_referenceFiberSum (readouts base noQuantum I)
    (unitary.execute Reference state) (fun entry _ => observed entry.1)
    leftRef rightRef).trans ?_)
  let indicator := fun basis : (context base noQuantum I).register.Index =>
    if (terminalMeasurement I).readout
      (basisEquiv I (nativeECDLP_context_wires base noQuantum I) basis) = outcome
    then (1 : ℂ) else 0
  let oldWeight := fun store : Store (context base noQuantum I) =>
    weight (store.read (liftInput base noQuantum I input))
  have actualWeight (store : Store (context base noQuantum I))
      (basis : (context base noQuantum I).register.Index) :
      observed (Circuit.writeMeasurementPath (readouts base noQuantum I) store
        (Circuit.measurementBasisPath (readouts base noQuantum I) basis)) =
      oldWeight store * indicator basis := by
    dsimp only [observed, oldWeight, indicator]
    rw [nativeECDLP_measured_input, nativeECDLP_observed_outcome]
    exact congrArg
      (fun value : ℂ => weight (store.read (liftInput base noQuantum I input)) * value)
      (indicator_decision _ _ _ 1 0)
  simp only [actualWeight]
  refine (BasisSeeded.fiber_store_blocks (unitary.execute Reference state)
    (fun store basis => oldWeight store * indicator basis) leftRef rightRef).trans ?_
  rw [Finset.sum_comm]
  have stores :
      (∑ original : Store (context base noQuantum I),
        ∑ basis : (context base noQuantum I).register.Index,
          (oldWeight original * indicator basis) *
            ((unitary.execute Reference state).filterClassical
              (fun entry => entry.1 = original)).quantumMarginal.matrix
                (basis, leftRef) (basis, rightRef)) =
      ∑ original : Store (context base noQuantum I), ((outcomePMF I B A outcome).toReal : ℂ) *
        (oldWeight original *
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            (resetLabel base noQuantum I, leftRef) (resetLabel base noQuantum I, rightRef)) := by
    apply Finset.sum_congr rfl
    intro original _
    let coefficient := oldWeight original *
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (resetLabel base noQuantum I, leftRef) (resetLabel base noQuantum I, rightRef)
    have terms :
        (∑ basis : (context base noQuantum I).register.Index,
          (oldWeight original * indicator basis) *
            ((unitary.execute Reference state).filterClassical
              (fun entry => entry.1 = original)).quantumMarginal.matrix
                (basis, leftRef) (basis, rightRef)) =
        ∑ basis : (context base noQuantum I).register.Index, indicator basis *
          (((‖(evolvedState I B A).normalized
            (basisEquiv I (nativeECDLP_context_wires base noQuantum I) basis)‖ ^ 2 : ℝ) : ℂ) *
              coefficient) := by
      apply Finset.sum_congr rfl
      intro basis _
      rw [nativeECDLP_unitary_seed_entry base noQuantum I B A state seeded, source_weight]
      dsimp only [coefficient]
      ring
    refine terms.trans ((weighted_fiber _ _ _ coefficient).trans ?_)
    apply congrArg (fun probability : ℝ => (probability : ℂ) * coefficient)
    refine ((basisEquiv I (nativeECDLP_context_wires base noQuantum I)).sum_comp
      (fun basis => if (terminalMeasurement I).readout basis = outcome then
        ‖(evolvedState I B A).normalized basis‖ ^ 2 else 0)).trans ?_
    refine Eq.trans ?_
      (TerminalZMeasure.outcomePMF_toReal (terminalMeasurement I) (evolvedState I B A) outcome).symm
    apply Finset.sum_congr rfl
    intro basis _
    exact indicator_decision _ _ _ _ _
  refine stores.trans ?_
  rw [← Finset.mul_sum]
  exact congrArg (fun coefficient : ℂ => ((outcomePMF I B A outcome).toReal : ℂ) * coefficient)
    (BasisSeeded.referenceFiberSum_seed _ state seeded oldWeight leftRef rightRef).symm

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
