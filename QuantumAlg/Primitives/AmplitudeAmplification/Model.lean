/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Gates.Rotation.Operator
import all QuantumAlg.Components.Kets
import all QuantumAlg.Components.Oracle.Reflection
public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.State.Normalized
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Mathematical source data for amplitude amplification

The normalized good/bad plane, preparation unitary and exact trigonometric
states contain no implementation footprint or resource certificate. The
angle is any real number and the iteration count is any natural number
[dW19, qcnotes.tex:2914-2961]. Source access belongs to separate component
occurrences and the native execution.
-/

section

namespace QuantumAlg

open NormalizedVector

noncomputable section

/-- The angle after `k` amplitude-amplification iterates: `(2k+1)θ`. -/
def amplitudeAmplificationAngle (θ : ℝ) (k : ℕ) : ℝ := ((2 : ℝ) * k + 1) * θ

/-- The metadata-free normalized good/bad-plane state with bad amplitude
`cos((2k+1)θ)` and good amplitude `sin((2k+1)θ)`. -/
def amplitudeAmplificationState (θ : ℝ) (k : ℕ) : NormalizedVector (Qubits 1) :=
  NormalizedVector.ofVector
    (((Real.cos (amplitudeAmplificationAngle θ k) : ℂ) •
          (ket0 : HilbertVector (Qubits 1))) +
        ((Real.sin (amplitudeAmplificationAngle θ k) : ℂ) •
          (ket1 : HilbertVector (Qubits 1))))
    (by
      rw [NormalizedVector.norm_eq_two_terms]
      simp only [ket0, ket1, NormalizedVector.ket_apply,
        PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, Nat.reducePow]
      norm_num
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.normSq_ofReal,
        Complex.normSq_ofReal]
      simpa [add_comm, sq] using
        Real.cos_sq_add_sin_sq (amplitudeAmplificationAngle θ k))

@[simp]
lemma amplitudeAmplificationState_coe (θ : ℝ) (k : ℕ) :
    (amplitudeAmplificationState θ k : HilbertVector (Qubits 1)) =
      ((Real.cos (amplitudeAmplificationAngle θ k) : ℂ) •
          (ket0 : HilbertVector (Qubits 1))) +
        ((Real.sin (amplitudeAmplificationAngle θ k) : ℂ) •
          (ket1 : HilbertVector (Qubits 1))) := rfl

/-- One amplitude-amplification iterate on the good/bad plane: rotation by
`2θ`. Since `rotY φ` rotates the real plane by `φ/2`, this is `rotY (4θ)`. -/
def amplitudeAmplificationStep (θ : ℝ) : UnitaryOperator (Qubits 1) :=
  rotYOp (4 * θ)

/-- One amplification step increases the good/bad-plane angle by `2θ`. -/
private lemma amplitudeAmplificationStep_apply_state_coe (θ : ℝ) (k : ℕ) :
    HilbertOperator.applyVec
        (amplitudeAmplificationStep θ : HilbertOperator (Qubits 1))
        (amplitudeAmplificationState θ k : HilbertVector (Qubits 1)) =
      (amplitudeAmplificationState θ (k + 1) : HilbertVector (Qubits 1)) := by
  ext i
  have hangle : amplitudeAmplificationAngle θ (k + 1) =
      amplitudeAmplificationAngle θ k + 2 * θ := by
    unfold amplitudeAmplificationAngle
    norm_num
    ring
  fin_cases i
  · rw [HilbertOperator.applyVec_apply]
    simp only [amplitudeAmplificationStep, amplitudeAmplificationState,
      rotYOp, hangle, Nat.reducePow,
      Fin.sum_univ_two, ket0, ket1, Complex.ofReal_cos, Complex.ofReal_sin]
    norm_num
    rw [Complex.cos_add]
    ring_nf
  · rw [HilbertOperator.applyVec_apply]
    simp only [amplitudeAmplificationStep, amplitudeAmplificationState,
      rotYOp, hangle, Nat.reducePow,
      Fin.sum_univ_two, ket0, ket1, Complex.ofReal_cos, Complex.ofReal_sin]
    norm_num
    rw [Complex.sin_add]
    ring_nf

/-- One amplification step preserves normalization in its public type. -/
lemma amplitudeAmplificationStep_apply_state (θ : ℝ) (k : ℕ) :
    (amplitudeAmplificationStep θ).apply
        (amplitudeAmplificationState θ k) =
      amplitudeAmplificationState θ (k + 1) := by
  apply NormalizedVector.ext
  intro i
  exact congrArg (fun ψ : HilbertVector (Qubits 1) => ψ i)
    (amplitudeAmplificationStep_apply_state_coe θ k)

/-- Iterating the abstract amplification rotation gives the standard closed
form. -/
private lemma amplitudeAmplificationStep_pow_apply_coe (θ : ℝ) (k : ℕ) :
    HilbertOperator.applyVec
        ((amplitudeAmplificationStep θ : HilbertOperator (Qubits 1)) ^ k)
        (amplitudeAmplificationState θ 0 : HilbertVector (Qubits 1)) =
      (amplitudeAmplificationState θ k : HilbertVector (Qubits 1)) := by
  induction k with
  | zero =>
      simp [HilbertOperator.one_applyVec]
  | succ k ih =>
      rw [pow_succ', HilbertOperator.mul_applyVec, ih,
        amplitudeAmplificationStep_apply_state_coe]

/-- Iterated amplification preserves normalization in its public type. -/
lemma amplitudeAmplificationStep_pow_apply (θ : ℝ) (k : ℕ) :
    ((amplitudeAmplificationStep θ) ^ k).apply
        (amplitudeAmplificationState θ 0) =
      amplitudeAmplificationState θ k := by
  apply NormalizedVector.ext
  intro i
  exact congrArg (fun ψ : HilbertVector (Qubits 1) => ψ i)
    (amplitudeAmplificationStep_pow_apply_coe θ k)

/-- Intrinsic source data for amplitude amplification on an arbitrary
`n`-qubit register. The iterate is not an input: it is constructed from the
preparation operator and the rank-one reflections about `|0^n>` and the bad
state. -/
public structure IntrinsicAmplitudeAmplificationModel (n : Nat) where
  /-- Initial angle from the bad-state axis. -/
  θ : ℝ
  /-- Source preparation unitary `A`. -/
  preparation : UnitaryOperator (Qubits n)
  /-- Normalized good component `|psi_1>`. -/
  good : NormalizedVector (Qubits n)
  /-- Normalized bad component `|psi_0>`. -/
  bad : NormalizedVector (Qubits n)
  /-- The good and bad components are orthogonal. -/
  good_bad_inner :
    inner ℂ (good : HilbertVector (Qubits n))
      (bad : HilbertVector (Qubits n)) = 0
  /-- `A|0^n> = sin theta |psi_1> + cos theta |psi_0>`. -/
  prepares_start :
    preparation.applyVec
        (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n)) :
          HilbertVector (Qubits n)) =
      ((Real.sin θ : ℂ) • (good : HilbertVector (Qubits n))) +
        ((Real.cos θ : ℂ) • (bad : HilbertVector (Qubits n)))

namespace IntrinsicAmplitudeAmplificationModel

/-- The all-zero computational basis state on the source register.

The model argument intentionally scopes this canonical state to the source
instance used by the surrounding construction; its mathematical value depends
only on the register size. -/
@[nolint unusedArguments]
def zeroKet {n : Nat} (_M : IntrinsicAmplitudeAmplificationModel n) :
    NormalizedVector (Qubits n) :=
  NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n))

lemma planeState_norm_eq_one {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (α : ℝ) :
    ‖((Real.sin α : ℂ) • (M.good : HilbertVector (Qubits n))) +
        ((Real.cos α : ℂ) • (M.bad : HilbertVector (Qubits n)))‖ = 1 := by
  have horth :
      inner ℂ ((Real.sin α : ℂ) • (M.good : HilbertVector (Qubits n)))
          ((Real.cos α : ℂ) • (M.bad : HilbertVector (Qubits n))) = 0 := by
    simp [inner_smul_left, inner_smul_right, M.good_bad_inner]
  have hsq :
      ‖((Real.sin α : ℂ) • (M.good : HilbertVector (Qubits n))) +
          ((Real.cos α : ℂ) • (M.bad : HilbertVector (Qubits n)))‖ ^ 2 = 1 := by
    calc
      _ = ‖(Real.sin α : ℂ) • (M.good : HilbertVector (Qubits n))‖ ^ 2 +
          ‖(Real.cos α : ℂ) • (M.bad : HilbertVector (Qubits n))‖ ^ 2 :=
        by simpa [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
      _ = 1 := by
        rw [norm_smul, norm_smul, M.good.norm_eq_one, M.bad.norm_eq_one,
          mul_one, mul_one]
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
          Complex.normSq_ofReal, Complex.normSq_ofReal]
        simpa [add_comm, sq] using Real.cos_sq_add_sin_sq α
  nlinarith [norm_nonneg
    (((Real.sin α : ℂ) • (M.good : HilbertVector (Qubits n))) +
      ((Real.cos α : ℂ) • (M.bad : HilbertVector (Qubits n))))]

/-- The source-level closed form at an arbitrary plane angle. -/
def stateAt {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (α : ℝ) :
    NormalizedVector (Qubits n) :=
  NormalizedVector.ofVector
    (((Real.sin α : ℂ) • (M.good : HilbertVector (Qubits n))) +
      ((Real.cos α : ℂ) • (M.bad : HilbertVector (Qubits n))))
    (planeState_norm_eq_one M α)

@[simp]
lemma stateAt_coe {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (α : ℝ) :
    (M.stateAt α : HilbertVector (Qubits n)) =
      ((Real.sin α : ℂ) • (M.good : HilbertVector (Qubits n))) +
        ((Real.cos α : ℂ) • (M.bad : HilbertVector (Qubits n))) := rfl

/-- The source-level closed form after `k` amplification iterates. -/
public def amplifiedState {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) : NormalizedVector (Qubits n) :=
  M.stateAt (amplitudeAmplificationAngle M.θ k)

@[simp]
lemma amplifiedState_coe {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    (M.amplifiedState k : HilbertVector (Qubits n)) =
      (M.stateAt (amplitudeAmplificationAngle M.θ k) :
        HilbertVector (Qubits n)) := rfl

lemma bad_good_inner {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) :
    inner ℂ (M.bad : HilbertVector (Qubits n))
      (M.good : HilbertVector (Qubits n)) = 0 :=
  inner_eq_zero_symm.mp M.good_bad_inner

private lemma prepared_eq_amplifiedState_zero_coe {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) :
    M.preparation.applyVec (M.zeroKet : HilbertVector (Qubits n)) =
      (M.amplifiedState 0 : HilbertVector (Qubits n)) := by
  rw [zeroKet, M.prepares_start]
  simp [amplifiedState, stateAt, amplitudeAmplificationAngle]

/-- Source preparation produces the normalized initial amplification state. -/
lemma prepared_eq_amplifiedState_zero {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) :
    M.preparation.apply M.zeroKet = M.amplifiedState 0 := by
  apply NormalizedVector.ext
  intro i
  exact congrArg (fun ψ : HilbertVector (Qubits n) => ψ i)
    (prepared_eq_amplifiedState_zero_coe M)

private lemma eigenPlaneVec_norm_eq_one {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖invSqrt2 •
        ((M.good : HilbertVector (Qubits n)) +
          z • (M.bad : HilbertVector (Qubits n)))‖ = 1 := by
  have horth :
      inner ℂ (M.good : HilbertVector (Qubits n))
          (z • (M.bad : HilbertVector (Qubits n))) = 0 := by
    simp [inner_smul_right, M.good_bad_inner]
  have hsq :
      ‖(M.good : HilbertVector (Qubits n)) +
          z • (M.bad : HilbertVector (Qubits n))‖ ^ 2 = 2 := by
    calc
      _ = ‖(M.good : HilbertVector (Qubits n))‖ ^ 2 +
          ‖z • (M.bad : HilbertVector (Qubits n))‖ ^ 2 :=
        by simpa [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
      _ = 2 := by
        rw [M.good.norm_eq_one, norm_smul, hz, M.bad.norm_eq_one]
        norm_num
  have hnorm :
      ‖(M.good : HilbertVector (Qubits n)) +
          z • (M.bad : HilbertVector (Qubits n))‖ = Real.sqrt 2 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg 2)).mp
    rw [hsq, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  rw [norm_smul, norm_invSqrt2, hnorm,
    inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num))]

/-- Normalized positive-phase eigenstate `(good + i bad) / sqrt 2`
[Lin22, appqpe.tex:200-219]. -/
def eigenPlus {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) :
    NormalizedVector (Qubits n) :=
  NormalizedVector.ofVector
    (invSqrt2 •
      ((M.good : HilbertVector (Qubits n)) +
        Complex.I • (M.bad : HilbertVector (Qubits n)))) (by
    exact eigenPlaneVec_norm_eq_one M Complex.I (by simp))

/-- Normalized negative-phase eigenstate `(good - i bad) / sqrt 2`
[Lin22, appqpe.tex:200-219]. -/
def eigenMinus {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) :
    NormalizedVector (Qubits n) :=
  NormalizedVector.ofVector
    (invSqrt2 •
      ((M.good : HilbertVector (Qubits n)) +
        (-Complex.I) • (M.bad : HilbertVector (Qubits n)))) (by
    exact eigenPlaneVec_norm_eq_one M (-Complex.I) (by simp))

@[simp]
lemma eigenPlus_coe {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) :
    (M.eigenPlus : HilbertVector (Qubits n)) =
      invSqrt2 •
        ((M.good : HilbertVector (Qubits n)) +
          Complex.I • (M.bad : HilbertVector (Qubits n))) := rfl

@[simp]
lemma eigenMinus_coe {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) :
    (M.eigenMinus : HilbertVector (Qubits n)) =
      invSqrt2 •
        ((M.good : HilbertVector (Qubits n)) +
          (-Complex.I) • (M.bad : HilbertVector (Qubits n))) := rfl

/-- The two intrinsic phase eigenstates are orthogonal. -/
lemma eigenPlus_inner_eigenMinus {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) :
    inner ℂ (M.eigenPlus : HilbertVector (Qubits n))
      (M.eigenMinus : HilbertVector (Qubits n)) = 0 := by
  rw [eigenPlus_coe, eigenMinus_coe]
  have hgood :
      inner ℂ (M.good : HilbertVector (Qubits n))
          (M.good : HilbertVector (Qubits n)) = 1 :=
    inner_self_eq_one_of_norm_eq_one M.good.norm_eq_one
  have hbad :
      inner ℂ (M.bad : HilbertVector (Qubits n))
          (M.bad : HilbertVector (Qubits n)) = 1 :=
    inner_self_eq_one_of_norm_eq_one M.bad.norm_eq_one
  simp only [inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, hgood, hbad, M.good_bad_inner,
    M.bad_good_inner, starRingEnd_apply, mul_zero, add_zero, zero_add,
    mul_one, neg_mul]
  simp only [star_invSqrt2]
  simp only [Complex.star_def, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq, invSqrt2_sq]
  norm_num

/-- Orthogonality in the reverse inner-product order. -/
lemma eigenMinus_inner_eigenPlus {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) :
    inner ℂ (M.eigenMinus : HilbertVector (Qubits n))
      (M.eigenPlus : HilbertVector (Qubits n)) = 0 :=
  inner_eq_zero_symm.mp M.eigenPlus_inner_eigenMinus

/-- Coefficient of the positive-phase eigenstate in the prepared state. -/
def eigenPlusCoefficient {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) : ℂ :=
  invSqrt2 *
    ((Real.sin M.θ : ℂ) - (Real.cos M.θ : ℂ) * Complex.I)

/-- Coefficient of the negative-phase eigenstate in the prepared state. -/
def eigenMinusCoefficient {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) : ℂ :=
  invSqrt2 *
    ((Real.sin M.θ : ℂ) + (Real.cos M.θ : ℂ) * Complex.I)

/-- The positive-phase component has probability weight `1/2`. -/
lemma eigenPlusCoefficient_normSq {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) :
    Complex.normSq M.eigenPlusCoefficient = (1 : Real) / 2 := by
  have hinv : Complex.normSq invSqrt2 = (2 : Real)⁻¹ := by
    rw [Complex.normSq_eq_norm_sq, norm_sq_invSqrt2]
  have hphase :
      (Real.sin M.θ : ℂ) - (Real.cos M.θ : ℂ) * Complex.I =
        (Real.sin M.θ : ℂ) +
          ((-Real.cos M.θ : Real) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [eigenPlusCoefficient, Complex.normSq_mul, hinv, hphase,
    Complex.normSq_add_mul_I]
  rw [show Real.sin M.θ ^ 2 + (-Real.cos M.θ) ^ 2 = 1 by
    nlinarith [Real.cos_sq_add_sin_sq M.θ]]
  norm_num

/-- The negative-phase component has probability weight `1/2`. -/
lemma eigenMinusCoefficient_normSq {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) :
    Complex.normSq M.eigenMinusCoefficient = (1 : Real) / 2 := by
  have hinv : Complex.normSq invSqrt2 = (2 : Real)⁻¹ := by
    rw [Complex.normSq_eq_norm_sq, norm_sq_invSqrt2]
  rw [eigenMinusCoefficient, Complex.normSq_mul, hinv,
    Complex.normSq_add_mul_I]
  rw [show Real.sin M.θ ^ 2 + Real.cos M.θ ^ 2 = 1 by
    nlinarith [Real.cos_sq_add_sin_sq M.θ]]
  norm_num

/-- The prepared state is an equal-weight superposition of the two intrinsic
eigenstates, with phases determined by the initial angle. -/
lemma intrinsicPreparedState_eigen_decomposition {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) :
    M.preparation.applyVec (M.zeroKet : HilbertVector (Qubits n)) =
      M.eigenPlusCoefficient • (M.eigenPlus : HilbertVector (Qubits n)) +
        M.eigenMinusCoefficient • (M.eigenMinus : HilbertVector (Qubits n)) := by
  rw [zeroKet, M.prepares_start, eigenPlus_coe, eigenMinus_coe]
  apply WithLp.ofLp_injective
  funext i
  simp [eigenPlusCoefficient, eigenMinusCoefficient,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, smul_add]
  ring_nf
  rw [invSqrt2_sq, Complex.I_sq]
  ring

end IntrinsicAmplitudeAmplificationModel

end

end QuantumAlg

end
