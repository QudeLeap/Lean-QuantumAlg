/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.QPE.Basic
public import QuantumAlg.Primitives.AmplitudeAmplification.Construction
import all QuantumAlg.Algorithms.QPE.Basic
import all QuantumAlg.Primitives.AmplitudeAmplification.Construction
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Real.Pi.Bounds
public import QuantumAlg.Util.Real.LogCeiling

/-!
# Source domain and precision selection for amplitude estimation

The original intrinsic prepared-state domain retains its first-quadrant and
positive interior-probability promises. The two exact source eigenphases are
proved from the good-state reflection, and the precision/confidence parameters
select the same binary phase width [Lin22, appqpe.tex:189-254].
-/

namespace QuantumAlg.AmplitudeEstimation

noncomputable section

/-! ### Source promise and probability -/

/-- Good-state probability of the intrinsic prepared state. -/
public def targetProbability {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) : Real :=
  Real.sin M.θ ^ 2

/-- A fixed positive lower bound witnesses the public `p(1-p)=Omega(1)`
interior-probability promise. -/
def InteriorProbabilityPromise {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) : Prop :=
  ∃ c : Real,
    0 < c ∧ c <= targetProbability M * (1 - targetProbability M)

/-- Source-aligned input for general amplitude estimation.  The first-quadrant
contract makes the coefficients in `prepares_start` the nonnegative square
roots `sqrt p` and `sqrt (1-p)`, as in the public source statement. -/
public structure GeneralAmplitudeEstimationInput (n : Nat) where
  /-- Intrinsic source model whose prepared good-state probability is estimated. -/
  source : IntrinsicAmplitudeAmplificationModel n
  theta_nonneg : 0 <= source.θ
  theta_le_pi_div_two : source.θ <= Real.pi / 2
  /-- Positive lower bound supplied for `p * (1 - p)`. -/
  interiorLowerBound : Real
  interiorLowerBound_pos : 0 < interiorLowerBound
  interior_probability :
    interiorLowerBound <=
      targetProbability source * (1 - targetProbability source)

namespace GeneralAmplitudeEstimationInput

lemma interiorPromise {n : Nat} (E : GeneralAmplitudeEstimationInput n) :
    InteriorProbabilityPromise E.source :=
  ⟨E.interiorLowerBound, E.interiorLowerBound_pos, E.interior_probability⟩

lemma sin_theta_nonneg {n : Nat} (E : GeneralAmplitudeEstimationInput n) :
    0 <= Real.sin E.source.θ :=
  Real.sin_nonneg_of_nonneg_of_le_pi E.theta_nonneg
    (E.theta_le_pi_div_two.trans (by linarith [Real.pi_pos]))

lemma cos_theta_nonneg {n : Nat} (E : GeneralAmplitudeEstimationInput n) :
    0 <= Real.cos E.source.θ :=
  Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [E.theta_nonneg, Real.pi_pos]) E.theta_le_pi_div_two

/-- The intrinsic trigonometric preparation is exactly the source's
`sqrt p |psi_1> + sqrt (1-p) |psi_0>` decomposition. -/
lemma prepared_eq_sqrt_decomposition {n : Nat}
    (E : GeneralAmplitudeEstimationInput n) :
    E.source.preparation.applyVec
        (E.source.zeroKet : HilbertVector (Qubits n)) =
      ((Real.sqrt (targetProbability E.source) : Real) : Complex) •
          (E.source.good : HilbertVector (Qubits n)) +
        ((Real.sqrt (1 - targetProbability E.source) : Real) : Complex) •
          (E.source.bad : HilbertVector (Qubits n)) := by
  rw [IntrinsicAmplitudeAmplificationModel.zeroKet,
    E.source.prepares_start]
  have hsin : Real.sqrt (targetProbability E.source) =
      Real.sin E.source.θ := by
    rw [targetProbability, Real.sqrt_sq E.sin_theta_nonneg]
  have hcos_sq : 1 - targetProbability E.source =
      Real.cos E.source.θ ^ 2 := by
    rw [targetProbability]
    nlinarith [Real.cos_sq_add_sin_sq E.source.θ]
  have hcos : Real.sqrt (1 - targetProbability E.source) =
      Real.cos E.source.θ := by
    rw [hcos_sq, Real.sqrt_sq E.cos_theta_nonneg]
  rw [hsin, hcos]

end GeneralAmplitudeEstimationInput

/-! ### The two derived QPE eigenstate inputs -/

/-- Positive Grover eigenphase `theta/pi`, derived from the intrinsic source
step rather than accepted from the caller. -/
def positiveEigenInput {n : Nat} (E : GeneralAmplitudeEstimationInput n) :
    QPEEigenstateInput n where
  unitary := AmplitudeAmplification.intrinsicGoodSourceStepOperator E.source
  eigenstate := E.source.eigenPlus
  phase := E.source.θ / Real.pi
  eigenstate_eq := by
    rw [AmplitudeAmplification.intrinsicGoodSourceStepOperator_apply_eigenPlus]
    congr 2
    push_cast
    field_simp [Real.pi_ne_zero]

/-- Negative Grover eigenphase `-theta/pi`, derived from the same intrinsic
source step. -/
def negativeEigenInput {n : Nat} (E : GeneralAmplitudeEstimationInput n) :
    QPEEigenstateInput n where
  unitary := AmplitudeAmplification.intrinsicGoodSourceStepOperator E.source
  eigenstate := E.source.eigenMinus
  phase := -E.source.θ / Real.pi
  eigenstate_eq := by
    rw [AmplitudeAmplification.intrinsicGoodSourceStepOperator_apply_eigenMinus]
    congr 2
    push_cast
    field_simp [Real.pi_ne_zero]

/-! ### Precision and confidence selection -/

/-- A phase-window radius whose global `sin^2` decoding error is `eps`. -/
def precisionRadius (eps : Real) : Real := eps / Real.pi

/-- Integer target covered by the selected power-of-two phase grid. -/
def phaseScaleTarget (eps η : Real) : Nat :=
  Nat.ceil (η⁻¹ / precisionRadius eps)

/-- Canonical phase-register width selected from precision and confidence. -/
public def selectedPhaseQubits (eps η : Real) : Nat :=
  Nat.clog 2 (Nat.ceil (η⁻¹ / precisionRadius eps))

/-- The execution uses exactly the register width specified by the real logarithm. -/
public lemma selectedPhaseQubits_eq_logCeiling {eps η : Real}
    (heps : 0 < eps) (heta : 0 < η) :
    selectedPhaseQubits eps η = ⌈Real.logb 2 (Real.pi / (eps * η))⌉₊ := by
  have scale : η⁻¹ / precisionRadius eps = Real.pi / (eps * η) := by
    unfold precisionRadius
    field_simp [heps.ne', heta.ne']
  rw [selectedPhaseQubits, scale]
  exact RealLog.clog_ceil_eq_natCeil_logb (by decide)
    (div_pos Real.pi_pos (mul_pos heps heta))

lemma precisionRadius_pos {eps : Real} (heps : 0 < eps) :
    0 < precisionRadius eps := by
  exact div_pos heps Real.pi_pos

/-- The selected width satisfies the high-confidence QPE scale condition. -/
lemma selectedPhaseQubits_scale {eps η : Real}
    (heps : 0 < eps) (heta : 0 < η) :
    η⁻¹ <=
      (2 : Real) ^ selectedPhaseQubits eps η * precisionRadius eps := by
  let ρ := precisionRadius eps
  let N := Nat.ceil (η⁻¹ / ρ)
  have hrho : 0 < ρ := precisionRadius_pos heps
  have hceil : η⁻¹ / ρ <= (N : Real) := by
    simpa [N] using Nat.le_ceil (η⁻¹ / ρ)
  have hpowNat : N <= 2 ^ Nat.clog 2 N :=
    Nat.le_pow_clog (by omega : 1 < 2) N
  have hpowReal : (N : Real) <= (2 : Real) ^ Nat.clog 2 N := by
    exact_mod_cast hpowNat
  calc
    η⁻¹ = (η⁻¹ / ρ) * ρ := by
      field_simp [hrho.ne']
    _ <= (N : Real) * ρ :=
      mul_le_mul_of_nonneg_right hceil hrho.le
    _ <= (2 : Real) ^ Nat.clog 2 N * ρ :=
      mul_le_mul_of_nonneg_right hpowReal hrho.le
    _ = (2 : Real) ^ selectedPhaseQubits eps η *
        precisionRadius eps := by rfl

/-- Valid precision and confidence parameters always select a nonempty phase
register for every admitted execution. -/
lemma selectedPhaseQubits_pos {eps η : Real}
    (heps : 0 < eps) (heps_le : eps ≤ 1)
    (heta : 0 < η) (heta_le : η ≤ 1) :
    0 < selectedPhaseQubits eps η := by
  have hscale := selectedPhaseQubits_scale heps heta
  by_contra hpositive
  have hzero : selectedPhaseQubits eps η = 0 :=
    Nat.eq_zero_of_not_pos hpositive
  rw [hzero, pow_zero, one_mul] at hscale
  have hinverse : (1 : Real) ≤ η⁻¹ := by
    simpa using (inv_le_inv₀ (by norm_num : (0 : Real) < 1) heta).2 heta_le
  have hradius_lt : precisionRadius eps < 1 := by
    rw [precisionRadius]
    calc
      eps / Real.pi ≤ 1 / Real.pi :=
        div_le_div_of_nonneg_right heps_le Real.pi_pos.le
      _ < 1 := (div_lt_one Real.pi_pos).2 (by
        nlinarith [Real.pi_gt_three])
  linarith

end

end QuantumAlg.AmplitudeEstimation
