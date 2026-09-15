/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.AmplitudeEstimation.Basic
import all QuantumAlg.Algorithms.AmplitudeEstimation.Basic
import all QuantumAlg.Algorithms.QPE.Analysis
import all QuantumAlg.Algorithms.QPE.Basic
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Algorithms.QPE.WindowProbability
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Measure
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Primitives.AmplitudeAmplification.Construction
import all QuantumAlg.Util.Real.PeriodicSinSq

/-!
# Independent coherent source probability for amplitude estimation

The source-defined preparation and mathematical QPE operator evolve the
all-zero input into a coherent sum of its two exact Grover eigenbranches.
Orthogonality removes the cross
terms in each phase-register Born fiber, giving equal weights and the original
selected-width success bound [Lin22, appqpe.tex:189-254].

These are mathematical Born probabilities of the independent source target.
The native endpoint separately proves its actual elementary circuit operator
and derives stored Z outcomes from the single interpreter.
-/

namespace QuantumAlg.AmplitudeEstimation

open NormalizedVector
open scoped BigOperators

noncomputable section

/-- Metadata-free all-zero phase and source-register input. -/
def allZeroInput {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    NormalizedVector (Qubits (t + n)) :=
  (NormalizedVector.ket (R := Qubits t) (0 : Fin (2 ^ t))).tensor
    E.source.zeroKet

/-- Canonical mathematical all-zero input before the source preparation operator. -/
def inputState {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    QubitLayout.State (qpeLayout t n) where
  state := PureState.ofNormalized (allZeroInput E t)
    (qpeLayout t n).systemIdx
  system_idx_eq := rfl

/-- Independent source target: mathematical QPE after the source-granted preparation. -/
def sourceOperator {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    UnitaryOperator (Qubits (t + n)) :=
  (qpeCircuit t (AmplitudeAmplification.intrinsicGoodSourceStepOperator E.source)).matrix *
    UnitaryOperator.tensor (1 : UnitaryOperator (Qubits t)) E.source.preparation

/-- Normalized target state after the source-defined preparation and mathematical QPE. -/
def evolvedState {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    QubitLayout.State (qpeLayout t n) :=
  { state := PureState.ofNormalized
      ((sourceOperator E t).apply (allZeroInput E t))
      (qpeLayout t n).systemIdx
    system_idx_eq := rfl }

/-! ### Coherent prepared-state output distribution -/

/-- Decode a terminal phase-register outcome by the canonical big-endian
full-register decoder. -/
def decodedIndex {t : Nat}
    (outcome : TerminalZMeasure.Outcome t) : Fin (2 ^ t) :=
  TerminalZMeasure.fullRegisterIndex outcome

/-- Phase estimate in turns. -/
def decodedPhase {t : Nat}
    (outcome : TerminalZMeasure.Outcome t) : Real :=
  (decodedIndex outcome).val / (2 : Real) ^ t

/-- Probability estimate obtained from the measured phase register. -/
def estimate {t : Nat}
    (outcome : TerminalZMeasure.Outcome t) : Real :=
  periodicSinSq (decodedPhase outcome)

@[simp] theorem decodedIndex_qpeOutcome (t : Nat) (j : Fin (2 ^ t)) :
    decodedIndex (qpeOutcome t j) = j := by
  exact qpeOutcome_fullRegisterIndex t j

@[simp] theorem estimate_qpeOutcome (t : Nat) (j : Fin (2 ^ t)) :
    estimate (qpeOutcome t j) =
      periodicSinSq ((j.val : Real) / (2 : Real) ^ t) := by
  simp [estimate, decodedPhase]

theorem targetProbability_eq_periodicSinSq {n : Nat}
    (E : GeneralAmplitudeEstimationInput n) :
    targetProbability E.source =
      periodicSinSq (E.source.θ / Real.pi) := by
  unfold targetProbability periodicSinSq
  congr 2
  field_simp [Real.pi_ne_zero]

/-- The former exact-dyadic result remains only as a helper on the new
intrinsic source model; neither an eigenstate nor an index is a public input. -/
theorem exactDyadicEstimate_helper {n : Nat}
    (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    (j : Fin (2 ^ t))
    (hphase : E.source.θ / Real.pi =
      (j.val : Real) / (2 : Real) ^ t) :
    estimate (qpeOutcome t j) = targetProbability E.source := by
  rw [estimate_qpeOutcome, ← hphase, ← targetProbability_eq_periodicSinSq E]

/-- The prepared all-zero input evolves as the coherent sum of the positive
and negative QPE eigenbranches. -/
theorem sourceOperator_applyVec_allZero {n : Nat}
    (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    (sourceOperator E t).applyVec (allZeroInput E t : HilbertVector (Qubits (t + n))) =
      E.source.eigenPlusCoefficient •
          UnitaryCircuit.applyVec
            (qpeCircuit t (positiveEigenInput E).unitary)
            (qpeInput (positiveEigenInput E) t :
              HilbertVector (Qubits (t + n))) +
        E.source.eigenMinusCoefficient •
          UnitaryCircuit.applyVec
            (qpeCircuit t (negativeEigenInput E).unitary)
            (qpeInput (negativeEigenInput E) t :
              HilbertVector (Qubits (t + n))) := by
  rw [sourceOperator, UnitaryOperator.mul_applyVec]
  rw [allZeroInput, NormalizedVector.coe_tensor, UnitaryOperator.tensor_applyVec_tensor,
    UnitaryOperator.one_applyVec]
  rw [E.source.intrinsicPreparedState_eigen_decomposition]
  rw [HilbertVector.tensor_add, HilbertVector.tensor_smul, HilbertVector.tensor_smul]
  rw [UnitaryOperator.applyVec_add, UnitaryOperator.applyVec_smul,
    UnitaryOperator.applyVec_smul]
  rfl

/-- System-register slice at one measured phase index. -/
def phaseFiberState {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) (j : Fin (2 ^ t)) : HilbertVector (Qubits n) :=
  (E.source.eigenPlusCoefficient *
      phaseRegisterGeometricAmplitude t (positiveEigenInput E).phase j) •
      (E.source.eigenPlus : HilbertVector (Qubits n)) +
    (E.source.eigenMinusCoefficient *
      phaseRegisterGeometricAmplitude t (negativeEigenInput E).phase j) •
      (E.source.eigenMinus : HilbertVector (Qubits n))

/-- Coordinate form of the independent coherent source target. -/
theorem evolvedState_apply_prod {n : Nat}
    (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    (j : Fin (2 ^ t)) (y : Fin (2 ^ n)) :
    (evolvedState E t).normalized (prodEquiv (j, y)) =
      phaseFiberState E t j y := by
  change (sourceOperator E t).applyVec (allZeroInput E t : HilbertVector (Qubits (t + n)))
      (prodEquiv (j, y)) = _
  have hplus :
      UnitaryCircuit.applyVec (qpeCircuit t (positiveEigenInput E).unitary)
          (qpeInput (positiveEigenInput E) t :
            HilbertVector (Qubits (t + n))) =
        HilbertVector.tensor
          (UnitaryCircuit.applyNormalized (qpeReadoutCircuit t)
            (phaseState t (positiveEigenInput E).phase) :
            HilbertVector (Qubits t))
          ((positiveEigenInput E).eigenstate : HilbertVector (Qubits n)) := by
    simpa using congrArg
      (fun ψ : NormalizedVector (Qubits (t + n)) =>
        (ψ : HilbertVector (Qubits (t + n))))
      (qpeCircuit_applyNormalized_input (positiveEigenInput E) t)
  have hminus :
      UnitaryCircuit.applyVec (qpeCircuit t (negativeEigenInput E).unitary)
          (qpeInput (negativeEigenInput E) t :
            HilbertVector (Qubits (t + n))) =
        HilbertVector.tensor
          (UnitaryCircuit.applyNormalized (qpeReadoutCircuit t)
            (phaseState t (negativeEigenInput E).phase) :
            HilbertVector (Qubits t))
          ((negativeEigenInput E).eigenstate : HilbertVector (Qubits n)) := by
    simpa using congrArg
      (fun ψ : NormalizedVector (Qubits (t + n)) =>
        (ψ : HilbertVector (Qubits (t + n))))
      (qpeCircuit_applyNormalized_input (negativeEigenInput E) t)
  have hreadoutPlus :
      UnitaryCircuit.applyNormalized (qpeReadoutCircuit t)
          (phaseState t (positiveEigenInput E).phase) j =
        phaseRegisterGeometricAmplitude t
          (positiveEigenInput E).phase j := by
    change (invQFT t).apply (phaseState t (positiveEigenInput E).phase) j = _
    exact invQFT_phaseState_apply_geometricSum _ _ _
  have hreadoutMinus :
      UnitaryCircuit.applyNormalized (qpeReadoutCircuit t)
          (phaseState t (negativeEigenInput E).phase) j =
        phaseRegisterGeometricAmplitude t
          (negativeEigenInput E).phase j := by
    change (invQFT t).apply (phaseState t (negativeEigenInput E).phase) j = _
    exact invQFT_phaseState_apply_geometricSum _ _ _
  rw [sourceOperator_applyVec_allZero, hplus, hminus]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    HilbertVector.tensor_apply_prod, hreadoutPlus, hreadoutMinus]
  simp [positiveEigenInput, negativeEigenInput, phaseFiberState, mul_assoc]
  ring

/-- Orthogonality of the two Grover eigenbranches removes all coherent cross
terms in one phase-register fiber. -/
theorem phaseFiberState_norm_sq {n : Nat}
    (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    (j : Fin (2 ^ t)) :
    ‖phaseFiberState E t j‖ ^ 2 =
      1 / 2 *
          ‖phaseRegisterGeometricAmplitude t
            (positiveEigenInput E).phase j‖ ^ 2 +
        1 / 2 *
          ‖phaseRegisterGeometricAmplitude t
            (negativeEigenInput E).phase j‖ ^ 2 := by
  let a := E.source.eigenPlusCoefficient *
    phaseRegisterGeometricAmplitude t (positiveEigenInput E).phase j
  let b := E.source.eigenMinusCoefficient *
    phaseRegisterGeometricAmplitude t (negativeEigenInput E).phase j
  have horth :
      inner Complex
          (a • (E.source.eigenPlus : HilbertVector (Qubits n)))
          (b • (E.source.eigenMinus : HilbertVector (Qubits n))) = 0 := by
    simp only [inner_smul_left, inner_smul_right,
      E.source.eigenPlus_inner_eigenMinus, mul_zero]
  have hplus : ‖E.source.eigenPlusCoefficient‖ ^ 2 = (1 : Real) / 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact E.source.eigenPlusCoefficient_normSq
  have hminus : ‖E.source.eigenMinusCoefficient‖ ^ 2 = (1 : Real) / 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact E.source.eigenMinusCoefficient_normSq
  change ‖a • (E.source.eigenPlus : HilbertVector (Qubits n)) +
      b • (E.source.eigenMinus : HilbertVector (Qubits n))‖ ^ 2 = _
  calc
    _ = ‖a • (E.source.eigenPlus : HilbertVector (Qubits n))‖ ^ 2 +
          ‖b • (E.source.eigenMinus : HilbertVector (Qubits n))‖ ^ 2 := by
      simpa [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
    _ = _ := by
      rw [norm_smul, norm_smul, E.source.eigenPlus.norm_eq_one,
        E.source.eigenMinus.norm_eq_one, mul_one, mul_one]
      simp only [a, b, norm_mul, mul_pow]
      rw [hplus, hminus]

private theorem qpeOutcome_bijective (t : Nat) :
    Function.Bijective (qpeOutcome t) := by
  apply (Fintype.bijective_iff_injective_and_card (qpeOutcome t)).2
  refine ⟨qpeOutcome_injective t, ?_⟩
  simp

theorem qpeOutcome_fullRegisterIndex_inverse {t : Nat}
    (outcome : TerminalZMeasure.Outcome t) :
    qpeOutcome t (TerminalZMeasure.fullRegisterIndex outcome) = outcome := by
  obtain ⟨j, rfl⟩ := (qpeOutcome_bijective t).2 outcome
  simp

/-- The Born phase-register probability of the exact circuit state is the equal mixture of the
two orthogonal signed-eigenphase branches. -/
theorem outcome_probability_eq_eigen_mixture {n : Nat}
    (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    (j : Fin (2 ^ t)) :
    (qpeMeasurement t n).outcomePMF (evolvedState E t)
        (qpeOutcome t j) =
      ENNReal.ofReal
        (1 / 2 *
            ‖phaseRegisterGeometricAmplitude t
              (positiveEigenInput E).phase j‖ ^ 2 +
          1 / 2 *
            ‖phaseRegisterGeometricAmplitude t
              (negativeEigenInput E).phase j‖ ^ 2) := by
  rw [TerminalZMeasure.outcomePMF_apply, qpeMeasurement_fiber,
    Finset.sum_map]
  simp_rw [qpeFiberEmbedding_apply, evolvedState_apply_prod]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  rw [← EuclideanSpace.norm_sq_eq, phaseFiberState_norm_sq]

/-- The terminal outcome PMF of the exact joint preparation-plus-QPE state. -/
def outcomeDistribution {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) : PMF (TerminalZMeasure.Outcome t) :=
  (qpeMeasurement t n).outcomePMF (evolvedState E t)

/-- Pointwise, the exact terminal PMF is the half-and-half mixture of the two
signed eigenphase distributions. -/
theorem outcomeDistribution_eq_eigen_mixture {n : Nat}
    (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    (outcome : TerminalZMeasure.Outcome t) :
    outcomeDistribution E t outcome =
      ENNReal.ofReal (1 / 2) *
          (qpeMeasurement t n).outcomePMF
            (qpeEvolvedState (positiveEigenInput E) t) outcome +
        ENNReal.ofReal (1 / 2) *
          (qpeMeasurement t n).outcomePMF
            (qpeEvolvedState (negativeEigenInput E) t) outcome := by
  let j := TerminalZMeasure.fullRegisterIndex outcome
  have houtcome : qpeOutcome t j = outcome :=
    qpeOutcome_fullRegisterIndex_inverse outcome
  rw [outcomeDistribution, ← houtcome,
    outcome_probability_eq_eigen_mixture,
    qpeMeasurement_outcomePMF_apply,
    qpeMeasurement_outcomePMF_apply]
  rw [ENNReal.ofReal_add
      (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg (by norm_num) (sq_nonneg _)),
    ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 1 / 2),
    ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 1 / 2)]

/-! ### Signed-window success -/

/-- Additive-error success predicate on the decoded terminal outcome. -/
def SuccessfulOutcome {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (eps : Real) {t : Nat}
    (outcome : TerminalZMeasure.Outcome t) : Prop :=
  |estimate outcome - targetProbability E.source| <= eps

theorem positiveWindow_successful {n : Nat}
    (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    {eps : Real} (heps : 0 < eps)
    (outcome : TerminalZMeasure.Outcome t)
    (hwindow : QuantumPhaseEstimation.WithinPhaseWindow
      (positiveEigenInput E) t (precisionRadius eps) outcome) :
    SuccessfulOutcome E eps outcome := by
  have hcircle :
      ‖((decodedPhase outcome - E.source.θ / Real.pi : Real) :
          UnitAddCircle)‖ <= precisionRadius eps := by
    have h := le_of_lt hwindow
    simpa [QuantumPhaseEstimation.WithinPhaseWindow, qpePhaseDistance,
      positiveEigenInput, decodedPhase, decodedIndex, norm_sub_rev] using h
  rw [SuccessfulOutcome, estimate, targetProbability_eq_periodicSinSq E]
  calc
    |periodicSinSq (decodedPhase outcome) -
          periodicSinSq (E.source.θ / Real.pi)| <=
        Real.pi * precisionRadius eps :=
      periodicSinSq_error_of_signed_phase
        (E.source.θ / Real.pi) (decodedPhase outcome)
        (precisionRadius eps) (Or.inl hcircle)
    _ = eps := by
      rw [precisionRadius]
      field_simp [Real.pi_ne_zero]

theorem negativeWindow_successful {n : Nat}
    (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    {eps : Real} (heps : 0 < eps)
    (outcome : TerminalZMeasure.Outcome t)
    (hwindow : QuantumPhaseEstimation.WithinPhaseWindow
      (negativeEigenInput E) t (precisionRadius eps) outcome) :
    SuccessfulOutcome E eps outcome := by
  have hcircle :
      ‖((decodedPhase outcome + E.source.θ / Real.pi : Real) :
          UnitAddCircle)‖ <= precisionRadius eps := by
    have h := le_of_lt hwindow
    change ‖((-E.source.θ / Real.pi - decodedPhase outcome : Real) :
        UnitAddCircle)‖ <= precisionRadius eps at h
    have harg :
        -E.source.θ / Real.pi - decodedPhase outcome =
          -(decodedPhase outcome + E.source.θ / Real.pi) := by
      ring
    rw [harg, AddCircle.coe_neg, norm_neg] at h
    exact h
  rw [SuccessfulOutcome, estimate, targetProbability_eq_periodicSinSq E]
  calc
    |periodicSinSq (decodedPhase outcome) -
          periodicSinSq (E.source.θ / Real.pi)| <=
        Real.pi * precisionRadius eps :=
      periodicSinSq_error_of_signed_phase
        (E.source.θ / Real.pi) (decodedPhase outcome)
        (precisionRadius eps) (Or.inr hcircle)
    _ = eps := by
      rw [precisionRadius]
      field_simp [Real.pi_ne_zero]

/-- Event mass of the exact outcome PMF is the half-and-half mixture of the two
signed QPE branch event masses. -/
theorem outcomeProbability_eq_eigen_mixture {n : Nat}
    (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    (postcondition : TerminalZMeasure.Outcome t -> Prop) :
    (outcomeDistribution E t).toOuterMeasure
        {outcome | postcondition outcome} =
      ENNReal.ofReal (1 / 2) *
          ((qpeMeasurement t n).outcomePMF
            (qpeEvolvedState (positiveEigenInput E) t)).toOuterMeasure
              {outcome | postcondition outcome} +
        ENNReal.ofReal (1 / 2) *
          ((qpeMeasurement t n).outcomePMF
            (qpeEvolvedState (negativeEigenInput E) t)).toOuterMeasure
              {outcome | postcondition outcome} := by
  rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype,
    PMF.toOuterMeasure_apply_fintype]
  calc
    Finset.univ.sum (fun outcome =>
        Set.indicator {outcome | postcondition outcome}
          (outcomeDistribution E t) outcome) =
        Finset.univ.sum (fun outcome =>
          (ENNReal.ofReal (1 / 2) *
              Set.indicator {outcome | postcondition outcome}
                ((qpeMeasurement t n).outcomePMF
                  (qpeEvolvedState (positiveEigenInput E) t)) outcome +
            ENNReal.ofReal (1 / 2) *
              Set.indicator {outcome | postcondition outcome}
                ((qpeMeasurement t n).outcomePMF
                  (qpeEvolvedState (negativeEigenInput E) t)) outcome)) := by
      apply Finset.sum_congr rfl
      intro outcome houtcome
      by_cases hpost : postcondition outcome
      · simp only [Set.indicator_of_mem
          (s := {outcome | postcondition outcome}) hpost]
        exact outcomeDistribution_eq_eigen_mixture E t outcome
      · simp only [Set.indicator_of_notMem
          (s := {outcome | postcondition outcome}) hpost,
          mul_zero, add_zero]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private theorem phaseRegisterGeometricAmplitude_norm_sq_eq_one_of_sub_eq_int
    (t : Nat) (phase : Real) (j : Fin (2 ^ t)) (z : Int)
    (hphase : phase - (j.val : Real) / (2 : Real) ^ t = (z : Real)) :
    ‖phaseRegisterGeometricAmplitude t phase j‖ ^ 2 = 1 := by
  rw [phaseRegisterGeometricAmplitude_eq_principalError]
  have hprincipal : qpePrincipalError t phase j = 0 := by
    simp [qpePrincipalError, hphase]
  rw [hprincipal]
  have hamp : qpeErrorAmplitude t 0 = 1 := by
    simp [qpeErrorAmplitude]
  rw [hamp, norm_one]
  norm_num

private theorem qpeBranchOutcome_probability_one {n : Nat}
    (P : QPEEigenstateInput n) (t : Nat) (j : Fin (2 ^ t)) (z : Int)
    (hphase : P.phase - (j.val : Real) / (2 : Real) ^ t = (z : Real)) :
    (qpeMeasurement t n).outcomePMF (qpeEvolvedState P t)
        (qpeOutcome t j) = 1 := by
  rw [qpeMeasurement_outcomePMF_apply,
    phaseRegisterGeometricAmplitude_norm_sq_eq_one_of_sub_eq_int
      t P.phase j z hphase]
  norm_num

private theorem qpeBranch_successProbability_eq_one_of_exact_outcome {n : Nat}
    (P : QPEEigenstateInput n) (t : Nat)
    (postcondition : TerminalZMeasure.Outcome t → Prop)
    (j : Fin (2 ^ t))
    (hpoint : (qpeMeasurement t n).outcomePMF (qpeEvolvedState P t)
      (qpeOutcome t j) = 1)
    (hsuccess : postcondition (qpeOutcome t j)) :
    ((qpeMeasurement t n).outcomePMF
      (qpeEvolvedState P t)).toOuterMeasure
        {outcome | postcondition outcome} = 1 := by
  rw [PMF.toOuterMeasure_apply_eq_one_iff]
  intro outcome houtcome
  have hsupport :
      ((qpeMeasurement t n).outcomePMF
        (qpeEvolvedState P t)).support = {qpeOutcome t j} :=
    (PMF.apply_eq_one_iff _ _).mp hpoint
  have houtcome_eq : outcome = qpeOutcome t j := by
    rw [hsupport] at houtcome
    simpa using houtcome
  subst outcome
  exact hsuccess

/-- Exact signed-dyadic specialization of the prepared-state Born distribution.  The
two indices represent the positive and negative Grover phases modulo integer
turns.  Each measured QPE branch is deterministic at its signed index, so the
actual half-and-half mixture assigns probability one to the decoded success
event.  This helper does not add indices or certificates to the public input. -/
theorem exactDyadicBorn_successProbability_eq_one {n : Nat}
    (E : GeneralAmplitudeEstimationInput n) (eps η : Real)
    (heps : 0 <= eps)
    (jPlus jMinus : Fin (2 ^ selectedPhaseQubits eps η))
    (zPlus zMinus : Int)
    (hplus :
      (positiveEigenInput E).phase -
          (jPlus.val : Real) /
            (2 : Real) ^ selectedPhaseQubits eps η =
        (zPlus : Real))
    (hminus :
      (negativeEigenInput E).phase -
          (jMinus.val : Real) /
            (2 : Real) ^ selectedPhaseQubits eps η =
        (zMinus : Real)) :
    (outcomeDistribution E (selectedPhaseQubits eps η)).toOuterMeasure
        {outcome | SuccessfulOutcome E eps outcome} = 1 := by
  let t := selectedPhaseQubits eps η
  have hplusPhase :
      (positiveEigenInput E).phase =
        (jPlus.val : Real) / (2 : Real) ^ t + (zPlus : Real) := by
    dsimp [t]
    linarith
  have hminusPhase :
      (negativeEigenInput E).phase =
        (jMinus.val : Real) / (2 : Real) ^ t + (zMinus : Real) := by
    dsimp [t]
    linarith
  have hplusEstimate :
      estimate (qpeOutcome t jPlus) = targetProbability E.source := by
    rw [estimate_qpeOutcome, targetProbability_eq_periodicSinSq E]
    calc
      periodicSinSq ((jPlus.val : Real) / (2 : Real) ^ t) =
          periodicSinSq (positiveEigenInput E).phase := by
        rw [hplusPhase, periodicSinSq_add_int]
      _ = periodicSinSq (E.source.θ / Real.pi) := by
        rfl
  have hminusEstimate :
      estimate (qpeOutcome t jMinus) = targetProbability E.source := by
    rw [estimate_qpeOutcome, targetProbability_eq_periodicSinSq E]
    calc
      periodicSinSq ((jMinus.val : Real) / (2 : Real) ^ t) =
          periodicSinSq (negativeEigenInput E).phase := by
        rw [hminusPhase, periodicSinSq_add_int]
      _ = periodicSinSq (E.source.θ / Real.pi) := by
        rw [show (negativeEigenInput E).phase =
            -(E.source.θ / Real.pi) by
          simp only [negativeEigenInput]
          ring,
          periodicSinSq_neg]
  have hplusSuccessful :
      SuccessfulOutcome E eps (qpeOutcome t jPlus) := by
    rw [SuccessfulOutcome, hplusEstimate, sub_self, abs_zero]
    exact heps
  have hminusSuccessful :
      SuccessfulOutcome E eps (qpeOutcome t jMinus) := by
    rw [SuccessfulOutcome, hminusEstimate, sub_self, abs_zero]
    exact heps
  have hplusPoint := qpeBranchOutcome_probability_one
    (positiveEigenInput E) t jPlus zPlus (by simpa [t] using hplus)
  have hminusPoint := qpeBranchOutcome_probability_one
    (negativeEigenInput E) t jMinus zMinus (by simpa [t] using hminus)
  have hplusSuccess := qpeBranch_successProbability_eq_one_of_exact_outcome
    (positiveEigenInput E) t (SuccessfulOutcome E eps) jPlus
    hplusPoint hplusSuccessful
  have hminusSuccess := qpeBranch_successProbability_eq_one_of_exact_outcome
    (negativeEigenInput E) t (SuccessfulOutcome E eps) jMinus
    hminusPoint hminusSuccessful
  calc
    (outcomeDistribution E (selectedPhaseQubits eps η)).toOuterMeasure
        {outcome | SuccessfulOutcome E eps outcome} =
      ENNReal.ofReal (1 / 2) *
          ((qpeMeasurement t n).outcomePMF
            (qpeEvolvedState (positiveEigenInput E) t)).toOuterMeasure
              {outcome | SuccessfulOutcome E eps outcome} +
        ENNReal.ofReal (1 / 2) *
          ((qpeMeasurement t n).outcomePMF
            (qpeEvolvedState (negativeEigenInput E) t)).toOuterMeasure
              {outcome | SuccessfulOutcome E eps outcome} := by
      simpa [t] using outcomeProbability_eq_eigen_mixture
        E t (SuccessfulOutcome E eps)
    _ = ENNReal.ofReal (1 / 2) * 1 + ENNReal.ofReal (1 / 2) * 1 := by
      rw [hplusSuccess, hminusSuccess]
    _ = 1 := by
      rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num

private theorem qpeBranchWindowProbability_ge_one_sub_eta {n : Nat}
    (P : QPEEigenstateInput n) (t : Nat)
    (ρ η : Real) (hrho : 0 < ρ) (heta : 0 < η)
    (heta_le : η ≤ 1) (hscale : η⁻¹ ≤ (2 : Real) ^ t * ρ) :
    ENNReal.ofReal (1 - η) ≤
      ((qpeMeasurement t n).outcomePMF
        (qpeEvolvedState P t)).toOuterMeasure
          {outcome | QuantumPhaseEstimation.WithinPhaseWindow
            P t ρ outcome} := by
  exact QuantumPhaseEstimation.born_successProbability_ge_one_sub_eta
    P t ρ η hrho heta heta_le hscale

/-- The exact Born readout at the selected width succeeds with probability at least
`1-eta`; each signed QPE window is a subset of the same decoded success event. -/
theorem outcomeSuccessProbability_ge_one_sub_eta {n : Nat}
    (E : GeneralAmplitudeEstimationInput n)
    (eps η : Real) (_ht : 0 < selectedPhaseQubits eps η)
    (heps : 0 < eps) (heta : 0 < η)
    (heta_le : η <= 1) :
    ENNReal.ofReal (1 - η) <=
      (outcomeDistribution E (selectedPhaseQubits eps η)).toOuterMeasure
        {outcome | SuccessfulOutcome E eps outcome} := by
  let t := selectedPhaseQubits eps η
  let ρ := precisionRadius eps
  have hrho : 0 < ρ := precisionRadius_pos heps
  have hscale : η⁻¹ <= (2 : Real) ^ t * ρ := by
    simpa [t, ρ] using selectedPhaseQubits_scale heps heta
  have hplusWindow :=
    qpeBranchWindowProbability_ge_one_sub_eta
      (positiveEigenInput E) t ρ η hrho heta heta_le hscale
  have hminusWindow :=
    qpeBranchWindowProbability_ge_one_sub_eta
      (negativeEigenInput E) t ρ η hrho heta heta_le hscale
  have hplus : ENNReal.ofReal (1 - η) <=
      ((qpeMeasurement t n).outcomePMF
        (qpeEvolvedState (positiveEigenInput E) t)).toOuterMeasure
          {outcome | SuccessfulOutcome E eps outcome} := by
    exact hplusWindow.trans (by
      apply ((qpeMeasurement t n).outcomePMF
        (qpeEvolvedState (positiveEigenInput E) t)).toOuterMeasure.mono
      intro outcome hwindow
      exact positiveWindow_successful E t heps outcome hwindow)
  have hminus : ENNReal.ofReal (1 - η) <=
      ((qpeMeasurement t n).outcomePMF
        (qpeEvolvedState (negativeEigenInput E) t)).toOuterMeasure
          {outcome | SuccessfulOutcome E eps outcome} := by
    exact hminusWindow.trans (by
      apply ((qpeMeasurement t n).outcomePMF
        (qpeEvolvedState (negativeEigenInput E) t)).toOuterMeasure.mono
      intro outcome hwindow
      exact negativeWindow_successful E t heps outcome hwindow)
  rw [outcomeProbability_eq_eigen_mixture]
  calc
    ENNReal.ofReal (1 - η) =
        ENNReal.ofReal (1 / 2) * ENNReal.ofReal (1 - η) +
          ENNReal.ofReal (1 / 2) * ENNReal.ofReal (1 - η) := by
      rw [← add_mul, ← ENNReal.ofReal_add
        (by norm_num : (0 : Real) <= 1 / 2)
        (by norm_num : (0 : Real) <= 1 / 2)]
      norm_num
    _ <= _ := add_le_add
      (by gcongr)
      (by gcongr)

end

end QuantumAlg.AmplitudeEstimation
