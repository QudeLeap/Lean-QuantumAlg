/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.AmplitudeAmplification.Model
import all QuantumAlg.Primitives.AmplitudeAmplification.Model
import all QuantumAlg.Components.Oracle.Reflection
import all QuantumAlg.Core.Base

/-!
# Exact amplitude-amplification source mathematics

The two-reflection product advances every good/bad-plane angle by twice the
preparation angle. Both source reflection conventions have the same action
on that invariant plane; they are not identified on its orthogonal complement.
All statements retain arbitrary real angles and natural iteration counts.
-/

section

namespace QuantumAlg

open NormalizedVector

noncomputable section

namespace AmplitudeAmplification

/-- The source iterate constructed exactly as
`A (2|0><0|-I) A^dagger (2|psi_0><psi_0|-I)`
[Lin22, appqpe.tex:200-219]. -/
public def intrinsicSourceStepOperator {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) : UnitaryOperator (Qubits n) :=
  M.preparation *
    (OrthogonalProjector.rankOneReflectionOp M.zeroKet *
      (M.preparation.dagger *
        OrthogonalProjector.rankOneReflectionOp M.bad))

/-- Applying a unitary after its adjoint returns the original vector. -/
theorem unitary_applyVec_dagger_applyVec {n : Nat}
    (U : UnitaryOperator (Qubits n)) (ψ : HilbertVector (Qubits n)) :
    U.applyVec (U.dagger.applyVec ψ) = ψ := by
  change HilbertOperator.applyVec (U : HilbertOperator (Qubits n))
    (HilbertOperator.applyVec (U.dagger : HilbertOperator (Qubits n)) ψ) = ψ
  rw [← HilbertOperator.mul_applyVec]
  have hUU :
      (U : HilbertOperator (Qubits n)) *
          (U.dagger : HilbertOperator (Qubits n)) = 1 := by
    change (U : HilbertOperator (Qubits n)) *
        (U : HilbertOperator (Qubits n)).conjTranspose = 1
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp U.property
  rw [hUU, HilbertOperator.one_applyVec]

/-- Conjugating the all-zero rank-one reflection by `A` reflects through the
actually prepared state `A|0^n>`. -/
theorem intrinsicPreparedReflection_applyVec {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n)
    (φ : HilbertVector (Qubits n)) :
    M.preparation.applyVec
        ((OrthogonalProjector.rankOneReflectionOp M.zeroKet).applyVec
          (M.preparation.dagger.applyVec φ)) =
      ((2 : ℂ) *
          inner ℂ (M.preparation.applyVec (M.zeroKet : HilbertVector (Qubits n)))
            φ) •
        M.preparation.applyVec (M.zeroKet : HilbertVector (Qubits n)) - φ := by
  have hinner :
      inner ℂ (M.zeroKet : HilbertVector (Qubits n))
          (M.preparation.dagger.applyVec φ) =
        inner ℂ
          (M.preparation.applyVec (M.zeroKet : HilbertVector (Qubits n))) φ := by
    calc
      inner ℂ (M.zeroKet : HilbertVector (Qubits n))
          (M.preparation.dagger.applyVec φ) =
          inner ℂ
            (M.preparation.applyVec (M.zeroKet : HilbertVector (Qubits n)))
            (M.preparation.applyVec (M.preparation.dagger.applyVec φ)) := by
              symm
              exact M.preparation.inner_applyVec_applyVec
                (M.zeroKet : HilbertVector (Qubits n))
                (M.preparation.dagger.applyVec φ)
      _ = inner ℂ
          (M.preparation.applyVec (M.zeroKet : HilbertVector (Qubits n))) φ := by
            rw [unitary_applyVec_dagger_applyVec]
  rw [OrthogonalProjector.rankOneReflectionOp_applyVec,
    M.preparation.applyVec_sub, M.preparation.applyVec_smul,
    unitary_applyVec_dagger_applyVec, hinner]

/-- The source bad-state reflection fixes the bad component and negates the
orthogonal good component. -/
theorem intrinsicBadReflection_apply_stateAt {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (α : ℝ) :
    (OrthogonalProjector.rankOneReflectionOp M.bad).applyVec (M.stateAt α) =
      ((-(Real.sin α) : ℂ) • (M.good : HilbertVector (Qubits n))) +
        ((Real.cos α : ℂ) • (M.bad : HilbertVector (Qubits n))) := by
  have hinner :
      inner ℂ (M.bad : HilbertVector (Qubits n)) (M.stateAt α) =
        (Real.cos α : ℂ) := by
    rw [IntrinsicAmplitudeAmplificationModel.stateAt_coe]
    simp [inner_add_right,
      inner_smul_right, M.bad_good_inner, M.bad.norm_eq_one]
  rw [OrthogonalProjector.rankOneReflectionOp_applyVec, hinner]
  rw [IntrinsicAmplitudeAmplificationModel.stateAt_coe]
  module

/-- The good-state phase reflection `I - 2|psi_1><psi_1|` has the same
good/bad-plane action as reflection through the bad state. -/
theorem intrinsicGoodPhaseReflection_apply_stateAt {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (α : ℝ) :
    (OrthogonalProjector.rankOnePhaseReflectionOp M.good).applyVec
        (M.stateAt α) =
      ((-(Real.sin α) : ℂ) • (M.good : HilbertVector (Qubits n))) +
        ((Real.cos α : ℂ) • (M.bad : HilbertVector (Qubits n))) := by
  have hinner :
      inner ℂ (M.good : HilbertVector (Qubits n)) (M.stateAt α) =
        (Real.sin α : ℂ) := by
    rw [IntrinsicAmplitudeAmplificationModel.stateAt_coe]
    simp [inner_add_right,
      inner_smul_right, M.good.norm_eq_one, M.good_bad_inner]
  rw [OrthogonalProjector.rankOnePhaseReflectionOp_applyVec, hinner]
  rw [IntrinsicAmplitudeAmplificationModel.stateAt_coe]
  module

/-- On the complex span of the good/bad plane, phasing the good line and
reflecting through the bad line are the same transformation. No full-space
operator equality is claimed [Lin22, appqpe.tex:200-219]. -/
theorem intrinsicPlaneReflections_apply_plane_eq {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (a b : ℂ) :
    (OrthogonalProjector.rankOnePhaseReflectionOp M.good).applyVec
        (a • (M.good : HilbertVector (Qubits n)) +
          b • (M.bad : HilbertVector (Qubits n))) =
      (OrthogonalProjector.rankOneReflectionOp M.bad).applyVec
        (a • (M.good : HilbertVector (Qubits n)) +
          b • (M.bad : HilbertVector (Qubits n))) := by
  have hgoodInner :
      inner ℂ (M.good : HilbertVector (Qubits n))
          (a • (M.good : HilbertVector (Qubits n)) +
            b • (M.bad : HilbertVector (Qubits n))) = a := by
    simp [inner_add_right, inner_smul_right, M.good.norm_eq_one,
      M.good_bad_inner]
  have hbadInner :
      inner ℂ (M.bad : HilbertVector (Qubits n))
          (a • (M.good : HilbertVector (Qubits n)) +
            b • (M.bad : HilbertVector (Qubits n))) = b := by
    simp [inner_add_right, inner_smul_right, M.bad.norm_eq_one,
      M.bad_good_inner]
  rw [OrthogonalProjector.rankOnePhaseReflectionOp_applyVec,
    OrthogonalProjector.rankOneReflectionOp_applyVec, hgoodInner, hbadInner]
  module

/-- The trigonometric `stateAt` bridge is a corollary of the general
complex-linear good/bad-plane bridge. -/
private theorem intrinsicPlaneReflections_apply_stateAt_eq_coe {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (α : ℝ) :
    (OrthogonalProjector.rankOnePhaseReflectionOp M.good).applyVec
        (M.stateAt α) =
      (OrthogonalProjector.rankOneReflectionOp M.bad).applyVec
        (M.stateAt α) := by
  simpa [IntrinsicAmplitudeAmplificationModel.stateAt] using
    intrinsicPlaneReflections_apply_plane_eq M
      (Real.sin α : ℂ) (Real.cos α : ℂ)

/-- On a normalized plane state, the two reflection conventions agree as
normalized transformations. -/
theorem intrinsicPlaneReflections_apply_stateAt_eq {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (α : ℝ) :
    (OrthogonalProjector.rankOnePhaseReflectionOp M.good).apply
        (M.stateAt α) =
      (OrthogonalProjector.rankOneReflectionOp M.bad).apply
        (M.stateAt α) := by
  apply NormalizedVector.ext
  intro i
  exact congrArg (fun ψ : HilbertVector (Qubits n) => ψ i)
    (intrinsicPlaneReflections_apply_stateAt_eq_coe M α)

/-- The amplitude-estimation reflection convention
`A (2|0><0|-I) A^dagger (I-2|psi_1><psi_1|)`
[Lin22, appqpe.tex:200-219]. -/
def intrinsicGoodSourceStepOperator {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) : UnitaryOperator (Qubits n) :=
  M.preparation *
    (OrthogonalProjector.rankOneReflectionOp M.zeroKet *
      (M.preparation.dagger *
        OrthogonalProjector.rankOnePhaseReflectionOp M.good))

/-- The constructed source iterate advances every good/bad-plane angle by
`2 theta`; no caller-supplied rotation or eigen-equation is used. -/
private theorem intrinsicSourceStepOperator_apply_stateAt_coe {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (α : ℝ) :
    (intrinsicSourceStepOperator M).applyVec (M.stateAt α) =
      M.stateAt (α + 2 * M.θ) := by
  let reflected : HilbertVector (Qubits n) :=
    ((-(Real.sin α) : ℂ) • (M.good : HilbertVector (Qubits n))) +
      ((Real.cos α : ℂ) • (M.bad : HilbertVector (Qubits n)))
  have hreflected :
      (OrthogonalProjector.rankOneReflectionOp M.bad).applyVec (M.stateAt α) =
        reflected := intrinsicBadReflection_apply_stateAt M α
  have hgood :
      inner ℂ (M.good : HilbertVector (Qubits n))
          (M.good : HilbertVector (Qubits n)) = 1 :=
    inner_self_eq_one_of_norm_eq_one M.good.norm_eq_one
  have hbad :
      inner ℂ (M.bad : HilbertVector (Qubits n))
          (M.bad : HilbertVector (Qubits n)) = 1 :=
    inner_self_eq_one_of_norm_eq_one M.bad.norm_eq_one
  have hinner :
      inner ℂ
          (M.preparation.applyVec (M.zeroKet : HilbertVector (Qubits n)))
          reflected =
        (-(Real.sin M.θ : ℂ) * (Real.sin α : ℂ) +
          (Real.cos M.θ : ℂ) * (Real.cos α : ℂ)) := by
    have hstarSin :
        (starRingEnd ℂ) (Complex.sin (M.θ : ℂ)) =
          Complex.sin (M.θ : ℂ) := by
      rw [starRingEnd_apply, Complex.star_def, ← Complex.sin_conj,
        Complex.conj_ofReal]
    have hstarCos :
        (starRingEnd ℂ) (Complex.cos (M.θ : ℂ)) =
          Complex.cos (M.θ : ℂ) := by
      rw [starRingEnd_apply, Complex.star_def, ← Complex.cos_conj,
        Complex.conj_ofReal]
    rw [IntrinsicAmplitudeAmplificationModel.zeroKet, M.prepares_start]
    simp only [reflected, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, hgood, hbad, M.good_bad_inner, M.bad_good_inner,
      mul_one, mul_zero, add_zero, zero_add]
    simp only [Complex.ofReal_sin, neg_mul, Complex.ofReal_cos]
    rw [hstarSin, hstarCos]
    ring
  have hsin :
      2 * (-Real.sin M.θ * Real.sin α +
          Real.cos M.θ * Real.cos α) * Real.sin M.θ +
          Real.sin α =
        Real.sin (α + 2 * M.θ) := by
    rw [Real.sin_add, Real.sin_two_mul, Real.cos_two_mul_eq_one_sub]
    ring
  have hcos :
      2 * (-Real.sin M.θ * Real.sin α +
          Real.cos M.θ * Real.cos α) * Real.cos M.θ -
          Real.cos α =
        Real.cos (α + 2 * M.θ) := by
    rw [Real.cos_add, Real.sin_two_mul, Real.cos_two_mul]
    ring
  have hsinC :
      (2 : ℂ) *
          (-(Real.sin M.θ : ℂ) * (Real.sin α : ℂ) +
            (Real.cos M.θ : ℂ) * (Real.cos α : ℂ)) *
          (Real.sin M.θ : ℂ) + (Real.sin α : ℂ) =
        (Real.sin (α + 2 * M.θ) : ℂ) := by
    exact_mod_cast hsin
  have hcosC :
      (2 : ℂ) *
          (-(Real.sin M.θ : ℂ) * (Real.sin α : ℂ) +
            (Real.cos M.θ : ℂ) * (Real.cos α : ℂ)) *
          (Real.cos M.θ : ℂ) - (Real.cos α : ℂ) =
        (Real.cos (α + 2 * M.θ) : ℂ) := by
    exact_mod_cast hcos
  rw [intrinsicSourceStepOperator, UnitaryOperator.mul_applyVec,
    UnitaryOperator.mul_applyVec, UnitaryOperator.mul_applyVec, hreflected]
  rw [intrinsicPreparedReflection_applyVec, hinner,
    IntrinsicAmplitudeAmplificationModel.zeroKet, M.prepares_start]
  unfold reflected IntrinsicAmplitudeAmplificationModel.stateAt
  calc
    ((2 : ℂ) *
          (-(Real.sin M.θ : ℂ) * (Real.sin α : ℂ) +
            (Real.cos M.θ : ℂ) * (Real.cos α : ℂ))) •
          (((Real.sin M.θ : ℂ) •
              (M.good : HilbertVector (Qubits n))) +
            ((Real.cos M.θ : ℂ) •
              (M.bad : HilbertVector (Qubits n)))) -
        (((-(Real.sin α) : ℂ) •
              (M.good : HilbertVector (Qubits n))) +
          ((Real.cos α : ℂ) • (M.bad : HilbertVector (Qubits n)))) =
        (((2 : ℂ) *
              (-(Real.sin M.θ : ℂ) * (Real.sin α : ℂ) +
                (Real.cos M.θ : ℂ) * (Real.cos α : ℂ)) *
              (Real.sin M.θ : ℂ) + (Real.sin α : ℂ)) •
            (M.good : HilbertVector (Qubits n))) +
          (((2 : ℂ) *
              (-(Real.sin M.θ : ℂ) * (Real.sin α : ℂ) +
                (Real.cos M.θ : ℂ) * (Real.cos α : ℂ)) *
              (Real.cos M.θ : ℂ) - (Real.cos α : ℂ)) •
            (M.bad : HilbertVector (Qubits n))) := by module
    _ = ((Real.sin (α + 2 * M.θ) : ℂ) •
            (M.good : HilbertVector (Qubits n))) +
          ((Real.cos (α + 2 * M.θ) : ℂ) •
            (M.bad : HilbertVector (Qubits n))) := by rw [hsinC, hcosC]

/-- The constructed source iterate maps normalized plane states to normalized
plane states. -/
theorem intrinsicSourceStepOperator_apply_stateAt {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (α : ℝ) :
    (intrinsicSourceStepOperator M).apply (M.stateAt α) =
      M.stateAt (α + 2 * M.θ) := by
  apply NormalizedVector.ext
  intro i
  exact congrArg (fun ψ : HilbertVector (Qubits n) => ψ i)
    (intrinsicSourceStepOperator_apply_stateAt_coe M α)

/-- The exact source step sends the good axis to
`cos(2 theta) good - sin(2 theta) bad`
[Lin22, appqpe.tex:200-219]. -/
theorem intrinsicSourceStepOperator_apply_good {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) :
    (intrinsicSourceStepOperator M).applyVec
        (M.good : HilbertVector (Qubits n)) =
      ((Real.cos (2 * M.θ) : ℂ) •
          (M.good : HilbertVector (Qubits n))) +
        ((-Real.sin (2 * M.θ) : ℂ) •
          (M.bad : HilbertVector (Qubits n))) := by
  simpa [IntrinsicAmplitudeAmplificationModel.stateAt, Real.sin_add,
    Real.cos_add] using
    intrinsicSourceStepOperator_apply_stateAt_coe M (Real.pi / 2)

/-- The exact source step sends the bad axis to
`sin(2 theta) good + cos(2 theta) bad`
[Lin22, appqpe.tex:200-219]. -/
theorem intrinsicSourceStepOperator_apply_bad {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) :
    (intrinsicSourceStepOperator M).applyVec
        (M.bad : HilbertVector (Qubits n)) =
      ((Real.sin (2 * M.θ) : ℂ) •
          (M.good : HilbertVector (Qubits n))) +
        ((Real.cos (2 * M.θ) : ℂ) •
          (M.bad : HilbertVector (Qubits n))) := by
  simpa [IntrinsicAmplitudeAmplificationModel.stateAt] using
    intrinsicSourceStepOperator_apply_stateAt_coe M 0

/-- `(good + i bad) / sqrt 2` is the positive-phase eigenstate of the exact
source reflection product [Lin22, appqpe.tex:200-219]. -/
theorem intrinsicSourceStepOperator_apply_eigenPlus {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) :
    (intrinsicSourceStepOperator M).applyVec
        (M.eigenPlus : HilbertVector (Qubits n)) =
      Complex.exp ((2 * M.θ : Real) * Complex.I) •
        (M.eigenPlus : HilbertVector (Qubits n)) := by
  rw [IntrinsicAmplitudeAmplificationModel.eigenPlus_coe]
  rw [UnitaryOperator.applyVec_smul, UnitaryOperator.applyVec_add,
    UnitaryOperator.applyVec_smul, intrinsicSourceStepOperator_apply_good,
    intrinsicSourceStepOperator_apply_bad, exp_ofReal_mul_I]
  apply WithLp.ofLp_injective
  funext i
  simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `(good - i bad) / sqrt 2` is the negative-phase eigenstate of the exact
source reflection product [Lin22, appqpe.tex:200-219]. -/
theorem intrinsicSourceStepOperator_apply_eigenMinus {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) :
    (intrinsicSourceStepOperator M).applyVec
        (M.eigenMinus : HilbertVector (Qubits n)) =
      Complex.exp ((-(2 * M.θ) : Real) * Complex.I) •
        (M.eigenMinus : HilbertVector (Qubits n)) := by
  rw [IntrinsicAmplitudeAmplificationModel.eigenMinus_coe]
  rw [UnitaryOperator.applyVec_smul, UnitaryOperator.applyVec_add,
    UnitaryOperator.applyVec_smul, intrinsicSourceStepOperator_apply_good,
    intrinsicSourceStepOperator_apply_bad, exp_ofReal_mul_I]
  apply WithLp.ofLp_injective
  funext i
  simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Real.cos_neg, Real.sin_neg]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The amplitude-estimation convention advances the same good/bad-plane
angle as the source bad-reflection convention. -/
private theorem intrinsicGoodSourceStepOperator_apply_stateAt_coe {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (α : ℝ) :
    (intrinsicGoodSourceStepOperator M).applyVec (M.stateAt α) =
      M.stateAt (α + 2 * M.θ) := by
  rw [intrinsicGoodSourceStepOperator, UnitaryOperator.mul_applyVec,
    UnitaryOperator.mul_applyVec, UnitaryOperator.mul_applyVec,
    intrinsicPlaneReflections_apply_stateAt_eq_coe]
  simpa [intrinsicSourceStepOperator, UnitaryOperator.mul_applyVec] using
    intrinsicSourceStepOperator_apply_stateAt_coe M α

/-- The amplitude-estimation reflection convention also preserves normalized
plane states in its public contract. -/
theorem intrinsicGoodSourceStepOperator_apply_stateAt {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (α : ℝ) :
    (intrinsicGoodSourceStepOperator M).apply (M.stateAt α) =
      M.stateAt (α + 2 * M.θ) := by
  apply NormalizedVector.ext
  intro i
  exact congrArg (fun ψ : HilbertVector (Qubits n) => ψ i)
    (intrinsicGoodSourceStepOperator_apply_stateAt_coe M α)

/-- The amplitude-estimation step sends the good axis to
`cos(2 theta) good - sin(2 theta) bad`. -/
theorem intrinsicGoodSourceStepOperator_apply_good {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) :
    (intrinsicGoodSourceStepOperator M).applyVec
        (M.good : HilbertVector (Qubits n)) =
      ((Real.cos (2 * M.θ) : ℂ) •
          (M.good : HilbertVector (Qubits n))) +
        ((-Real.sin (2 * M.θ) : ℂ) •
          (M.bad : HilbertVector (Qubits n))) := by
  simpa [IntrinsicAmplitudeAmplificationModel.stateAt, Real.sin_add,
    Real.cos_add] using
    intrinsicGoodSourceStepOperator_apply_stateAt_coe M (Real.pi / 2)

/-- The amplitude-estimation step sends the bad axis to
`sin(2 theta) good + cos(2 theta) bad`. -/
theorem intrinsicGoodSourceStepOperator_apply_bad {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) :
    (intrinsicGoodSourceStepOperator M).applyVec
        (M.bad : HilbertVector (Qubits n)) =
      ((Real.sin (2 * M.θ) : ℂ) •
          (M.good : HilbertVector (Qubits n))) +
        ((Real.cos (2 * M.θ) : ℂ) •
          (M.bad : HilbertVector (Qubits n))) := by
  simpa [IntrinsicAmplitudeAmplificationModel.stateAt] using
    intrinsicGoodSourceStepOperator_apply_stateAt_coe M 0

/-- `(good + i bad) / sqrt 2` is the positive-phase eigenstate of the
amplitude-estimation reflection product [Lin22, appqpe.tex:200-219]. -/
theorem intrinsicGoodSourceStepOperator_apply_eigenPlus {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) :
    (intrinsicGoodSourceStepOperator M).applyVec
        (M.eigenPlus : HilbertVector (Qubits n)) =
      Complex.exp ((2 * M.θ : Real) * Complex.I) •
        (M.eigenPlus : HilbertVector (Qubits n)) := by
  rw [IntrinsicAmplitudeAmplificationModel.eigenPlus_coe]
  rw [UnitaryOperator.applyVec_smul, UnitaryOperator.applyVec_add,
    UnitaryOperator.applyVec_smul,
    intrinsicGoodSourceStepOperator_apply_good,
    intrinsicGoodSourceStepOperator_apply_bad, exp_ofReal_mul_I]
  apply WithLp.ofLp_injective
  funext i
  simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `(good - i bad) / sqrt 2` is the negative-phase eigenstate of the
amplitude-estimation reflection product [Lin22, appqpe.tex:200-219]. -/
theorem intrinsicGoodSourceStepOperator_apply_eigenMinus {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) :
    (intrinsicGoodSourceStepOperator M).applyVec
        (M.eigenMinus : HilbertVector (Qubits n)) =
      Complex.exp ((-(2 * M.θ) : Real) * Complex.I) •
        (M.eigenMinus : HilbertVector (Qubits n)) := by
  rw [IntrinsicAmplitudeAmplificationModel.eigenMinus_coe]
  rw [UnitaryOperator.applyVec_smul, UnitaryOperator.applyVec_add,
    UnitaryOperator.applyVec_smul,
    intrinsicGoodSourceStepOperator_apply_good,
    intrinsicGoodSourceStepOperator_apply_bad, exp_ofReal_mul_I]
  apply WithLp.ofLp_injective
  funext i
  simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Real.cos_neg, Real.sin_neg]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- One constructed source step advances the closed form from `k` to `k+1`. -/
private theorem intrinsicSourceStepOperator_apply_amplifiedState_coe {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    (intrinsicSourceStepOperator M).applyVec (M.amplifiedState k) =
      M.amplifiedState (k + 1) := by
  rw [IntrinsicAmplitudeAmplificationModel.amplifiedState,
    intrinsicSourceStepOperator_apply_stateAt_coe]
  unfold IntrinsicAmplitudeAmplificationModel.amplifiedState
  congr 1
  unfold amplitudeAmplificationAngle
  push_cast
  ring

/-- One source step maps the normalized closed form at `k` to that at `k+1`. -/
theorem intrinsicSourceStepOperator_apply_amplifiedState {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    (intrinsicSourceStepOperator M).apply (M.amplifiedState k) =
      M.amplifiedState (k + 1) := by
  apply NormalizedVector.ext
  intro i
  exact congrArg (fun ψ : HilbertVector (Qubits n) => ψ i)
    (intrinsicSourceStepOperator_apply_amplifiedState_coe M k)

/-- Iterating the constructed source operator gives the general `n`-qubit
closed form. -/
private theorem intrinsicSourceStepOperator_pow_apply_coe {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    HilbertOperator.applyVec
        ((intrinsicSourceStepOperator M : HilbertOperator (Qubits n)) ^ k)
        (M.amplifiedState 0) = M.amplifiedState k := by
  induction k with
  | zero => simp [HilbertOperator.one_applyVec]
  | succ k ih =>
      rw [pow_succ', HilbertOperator.mul_applyVec, ih]
      exact intrinsicSourceStepOperator_apply_amplifiedState_coe M k

/-- Iterating the source operator preserves normalization in its public type. -/
theorem intrinsicSourceStepOperator_pow_apply {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    ((intrinsicSourceStepOperator M) ^ k).apply (M.amplifiedState 0) =
      M.amplifiedState k := by
  apply NormalizedVector.ext
  intro i
  exact congrArg (fun ψ : HilbertVector (Qubits n) => ψ i)
    (intrinsicSourceStepOperator_pow_apply_coe M k)

/-- One good-reflection source step advances the closed form from `k` to `k+1`. -/
private theorem intrinsicGoodSourceStepOperator_apply_amplifiedState_coe {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    (intrinsicGoodSourceStepOperator M).applyVec (M.amplifiedState k) =
      M.amplifiedState (k + 1) := by
  rw [IntrinsicAmplitudeAmplificationModel.amplifiedState,
    intrinsicGoodSourceStepOperator_apply_stateAt_coe]
  unfold IntrinsicAmplitudeAmplificationModel.amplifiedState
  congr 1
  unfold amplitudeAmplificationAngle
  push_cast
  ring

/-- One source step maps the normalized closed form at `k` to that at `k+1`. -/
theorem intrinsicGoodSourceStepOperator_apply_amplifiedState {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    (intrinsicGoodSourceStepOperator M).apply (M.amplifiedState k) =
      M.amplifiedState (k + 1) := by
  apply NormalizedVector.ext
  intro i
  exact congrArg (fun ψ : HilbertVector (Qubits n) => ψ i)
    (intrinsicGoodSourceStepOperator_apply_amplifiedState_coe M k)

/-- Iterating the good-reflection source operator gives the general `n`-qubit
closed form. -/
private theorem intrinsicGoodSourceStepOperator_pow_apply_coe {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    HilbertOperator.applyVec
        ((intrinsicGoodSourceStepOperator M : HilbertOperator (Qubits n)) ^ k)
        (M.amplifiedState 0) = M.amplifiedState k := by
  induction k with
  | zero => simp [HilbertOperator.one_applyVec]
  | succ k ih =>
      rw [pow_succ', HilbertOperator.mul_applyVec, ih]
      exact intrinsicGoodSourceStepOperator_apply_amplifiedState_coe M k

/-- Iterating the source operator preserves normalization in its public type. -/
theorem intrinsicGoodSourceStepOperator_pow_apply {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    ((intrinsicGoodSourceStepOperator M) ^ k).apply (M.amplifiedState 0) =
      M.amplifiedState k := by
  apply NormalizedVector.ext
  intro i
  exact congrArg (fun ψ : HilbertVector (Qubits n) => ψ i)
    (intrinsicGoodSourceStepOperator_pow_apply_coe M k)

/-- The source's exact all-k rotation, independent of any execution representation. -/
public theorem source_rotation {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) :
    ((intrinsicSourceStepOperator M) ^ k).apply
      (M.preparation.apply (NormalizedVector.ket (R := Qubits n) 0)) =
        M.amplifiedState k := by
  change ((intrinsicSourceStepOperator M) ^ k).apply (M.preparation.apply M.zeroKet) = _
  rw [M.prepared_eq_amplifiedState_zero]
  exact intrinsicSourceStepOperator_pow_apply M k

end AmplitudeAmplification

end

end QuantumAlg

end
