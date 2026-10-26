/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base
import all QuantumAlg.Core.Base
import all QuantumAlg.Core.Base.State.Basic
import all QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Util.FinPow
public import QuantumAlg.Components.Oracle.TimeEvolution
import all QuantumAlg.Components.Oracle.TimeEvolution
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Spectral inverse-solution analysis

A finite eigenpair expansion yields the normalized inverse solution and controlled-rotation
  coefficient bounds.
The inverse normalization follows [HHL09, 08113171.tex:293-308].
The statements describe exact linear algebra and contain no implemented HHL run.
-/

section

namespace QuantumAlg

open scoped BigOperators

/-! ### Linear system model -/

/-- A sparse Hermitian matrix, normalized right-hand side and positive analysis parameters. -/
public structure LinearSystem (R : Register) (s : ℕ) where
  /-- The sparse Hermitian system matrix `A`. -/
  A : HilbertOperator R
  /-- The right-hand-side vector `b`. -/
  b : NormalizedVector R
  /-- Positive scale used in the eigenvalue-gap hypothesis. -/
  κ : ℝ
  hA_hermitian : A.IsHermitian
  hA_sparse : ∀ x : R.Index,
    (Finset.filter (fun y : R.Index => A x y ≠ 0) Finset.univ).card ≤ s
  hκ_pos : 0 < κ

namespace LinearSystem

variable {R : Register} {s : ℕ} (sys : LinearSystem R s)

public lemma κ_pos : 0 < sys.κ := sys.hκ_pos

public lemma A_hermitian : sys.A.IsHermitian := sys.hA_hermitian

public lemma A_sparse : ∀ x : R.Index,
    (Finset.filter (fun y : R.Index => sys.A x y ≠ 0) Finset.univ).card ≤ s := sys.hA_sparse

public lemma b_normalized : ‖(sys.b : HilbertVector R)‖ = 1 := sys.b.norm_eq_one

/-- The system matrix bundled as a Hamiltonian. -/
public def hamiltonian : Hamiltonian R :=
  ⟨sys.A, sys.hA_hermitian⟩

/-- Exact mathematical evolution with the positive phase convention.

`timeEvolutionOp H t` uses the convention `exp(-i t H)`, so the HHL
`exp(i A t)` convention is represented by time `-t`. -/
public noncomputable def hamiltonianSimulationUnitaryOperator (t : ℝ) : UnitaryOperator R :=
  timeEvolution sys.hamiltonian (-t)

@[simp]
public lemma coe_hamiltonianSimulationUnitaryOperator (t : ℝ) :
    ((sys.hamiltonianSimulationUnitaryOperator t : UnitaryOperator R) : HilbertOperator R)
      = timeEvolutionOp sys.A (-t) :=
  (rfl)

end LinearSystem

/-- The HHL controlled-rotation constant `C = 1/(2κ)`. -/
public noncomputable def inversionConstant (κ : ℝ) : ℝ := 1 / (2 * κ)

/-! ### Supplied eigenpair expansion

The finite eigenpair expansion and a lower bound on the absolute eigenvalues
are inputs. No orthogonality, complete spectral theorem or algorithm is inferred
from this record. -/

/-- A supplied finite eigenpair expansion of the right-hand side with a gap and nonzero inverse
  solution. -/
public structure LinearSystem.SpectralData {R : Register} {s : ℕ} (sys : LinearSystem R s) where
  /-- Finite index type for the supplied expansion. -/
  ι : Type
  /-- The expansion index type is finite. -/
  [fintype : Fintype ι]
  /-- Eigenvectors of the system matrix. -/
  eigenvector : ι → HilbertVector R
  /-- Real eigenvalues of the Hermitian system matrix. -/
  eigenvalue : ι → ℝ
  /-- Coefficients in the supplied expansion. -/
  coeff : ι → ℂ
  /-- Eigenvector equation for each indexed eigenpair. -/
  eigen_apply :
    ∀ j, WithLp.toLp 2 (sys.A.mulVec (eigenvector j).ofLp) =
      (eigenvalue j : ℂ) • eigenvector j
  /-- Expansion of the input state in the indexed eigenbasis. -/
  input_expansion : (sys.b : HilbertVector R) = ∑ j, coeff j • eigenvector j
  /-- HHL condition-number gap, phrased on the indexed eigenvalues. -/
  gap : ∀ j, 1 / sys.κ ≤ |eigenvalue j|
  /-- The inverse-solution vector is nonzero, so it can later be normalized. -/
  inverse_nonzero : (∑ j, (coeff j / (eigenvalue j : ℂ)) • eigenvector j) ≠ 0

attribute [instance] LinearSystem.SpectralData.fintype

namespace LinearSystem.SpectralData

variable {R : Register} {s : ℕ} {sys : LinearSystem R s}

/-- The unnormalized solution vector `A^{-1} b` represented in the spectral basis. -/
public noncomputable def inverseSolutionVec (D : LinearSystem.SpectralData sys) : HilbertVector R :=
  ∑ j, (D.coeff j / (D.eigenvalue j : ℂ)) • D.eigenvector j

/-- The inverse-solution vector is nonzero by the spectral-data hypothesis. -/
public lemma inverseSolutionVec_ne_zero (D : LinearSystem.SpectralData sys) :
    D.inverseSolutionVec ≠ 0 := by
  simpa [inverseSolutionVec] using D.inverse_nonzero

/-- The real eigenvalues in the spectral data are nonzero by the condition-number gap. -/
public lemma eigenvalue_ne_zero (D : LinearSystem.SpectralData sys) (j : D.ι) :
    (D.eigenvalue j : ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  have hpos : 0 < |D.eigenvalue j| := by
    exact lt_of_lt_of_le (one_div_pos.mpr sys.hκ_pos) (D.gap j)
  exact abs_pos.mp hpos

/-- The controlled-rotation amplitude `C / eigenvalue_j` is bounded by `1/2`. -/
public lemma inversionCoefficient_abs_le_half (D : LinearSystem.SpectralData sys) (j : D.ι) :
    |inversionConstant sys.κ / D.eigenvalue j| ≤ 1 / 2 := by
  unfold inversionConstant
  have hkappa_nonneg : 0 ≤ sys.κ := le_of_lt sys.hκ_pos
  have hlambda_abs_pos : 0 < |D.eigenvalue j| := by
    exact lt_of_lt_of_le (one_div_pos.mpr sys.hκ_pos) (D.gap j)
  have hprod : 1 ≤ sys.κ * |D.eigenvalue j| := by
    have h := mul_le_mul_of_nonneg_left (D.gap j) hkappa_nonneg
    field_simp [ne_of_gt sys.hκ_pos] at h
    rwa [div_self (ne_of_gt sys.hκ_pos)] at h
  have hden : 2 ≤ 2 * (sys.κ * |D.eigenvalue j|) := by
    nlinarith
  have htarget : 1 / (2 * (sys.κ * |D.eigenvalue j|)) ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by positivity) hden
  calc
    |(1 / (2 * sys.κ)) / D.eigenvalue j|
        = 1 / (2 * (sys.κ * |D.eigenvalue j|)) := by
          have hnum_pos : 0 < 1 / (2 * sys.κ) :=
            one_div_pos.mpr (mul_pos (by norm_num) sys.hκ_pos)
          rw [abs_div, abs_of_pos hnum_pos]
          field_simp [ne_of_gt sys.hκ_pos, ne_of_gt hlambda_abs_pos]
    _ ≤ 1 / 2 := htarget

/-- Applying `A` to the unnormalized inverse-solution vector recovers `b`. -/
public lemma applyVec_inverseSolutionVec (D : LinearSystem.SpectralData sys) :
    WithLp.toLp 2 (sys.A.mulVec D.inverseSolutionVec.ofLp) = (sys.b : HilbertVector R) := by
  change HilbertOperator.applyVec sys.A (D.inverseSolutionVec) = (sys.b : HilbertVector R)
  rw [D.input_expansion]
  unfold inverseSolutionVec
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [HilbertOperator.applyVec_smul]
  change (D.coeff j / (D.eigenvalue j : ℂ)) •
    WithLp.toLp 2 (sys.A.mulVec (D.eigenvector j).ofLp) = _
  rw [D.eigen_apply]
  have hEig : (D.eigenvalue j : ℂ) ≠ 0 := D.eigenvalue_ne_zero j
  rw [smul_smul, div_mul_cancel₀ _ hEig]

/-- The inverse-solution direction, certified to have norm one. -/
public noncomputable def normalizedSolutionState (D : LinearSystem.SpectralData sys) :
  NormalizedVector R
  :=
  NormalizedVector.ofNeZero D.inverseSolutionVec D.inverseSolutionVec_ne_zero

/-- Coercing the normalized target gives the explicit inverse-norm scaling. -/
public lemma normalizedSolutionState_coe (D : LinearSystem.SpectralData sys) :
    (D.normalizedSolutionState : HilbertVector R) =
      ((‖D.inverseSolutionVec‖ : ℂ)⁻¹) • D.inverseSolutionVec := (rfl)

/-- The normalized solution satisfies the rescaled linear system. -/
public lemma applyVec_normalizedSolutionState (D : LinearSystem.SpectralData sys) :
    WithLp.toLp 2 (sys.A.mulVec D.normalizedSolutionState.vec.ofLp) =
      ((‖D.inverseSolutionVec‖ : ℂ)⁻¹) • (sys.b : HilbertVector R) := by
  change HilbertOperator.applyVec sys.A (D.normalizedSolutionState : HilbertVector R) =
      ((‖D.inverseSolutionVec‖ : ℂ)⁻¹) • (sys.b : HilbertVector R)
  rw [normalizedSolutionState_coe, HilbertOperator.applyVec_smul]
  exact congrArg (fun v : HilbertVector R => (‖D.inverseSolutionVec‖ : ℂ)⁻¹ • v)
    D.applyVec_inverseSolutionVec

/-- The spectral coefficient expression `Σ_j β_j (C/λ_j) v_j`. -/
public noncomputable def postSelectionGoodComponent (D : LinearSystem.SpectralData sys) :
  HilbertVector R
  :=
  ∑ j, (D.coeff j * ((inversionConstant sys.κ : ℂ) / (D.eigenvalue j : ℂ))) •
    D.eigenvector j

/-- The spectral good-component expression equals the inverse solution scaled by `C`. -/
public lemma postSelectionGoodComponent_eq_scaled_inverse (D : LinearSystem.SpectralData sys) :
    D.postSelectionGoodComponent =
      (inversionConstant sys.κ : ℂ) • D.inverseSolutionVec := by
  unfold postSelectionGoodComponent inverseSolutionVec
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul]
  ring_nf

/-- The post-selected good component is nonzero. -/
public lemma postSelectionGoodComponent_ne_zero (D : LinearSystem.SpectralData sys) :
    D.postSelectionGoodComponent ≠ 0 := by
  rw [postSelectionGoodComponent_eq_scaled_inverse]
  apply smul_ne_zero
  · apply Complex.ofReal_ne_zero.mpr
    unfold inversionConstant
    have hden : (2 : ℝ) * sys.κ ≠ 0 :=
      mul_ne_zero (by norm_num) (ne_of_gt sys.hκ_pos)
    exact one_div_ne_zero hden
  · exact D.inverseSolutionVec_ne_zero

/-- Applying `A` to the good component gives the input state scaled by `C`. -/
public lemma applyVec_postSelectionGoodComponent (D : LinearSystem.SpectralData sys) :
    WithLp.toLp 2 (sys.A.mulVec D.postSelectionGoodComponent.ofLp) =
      (inversionConstant sys.κ : ℂ) • (sys.b : HilbertVector R) := by
  change HilbertOperator.applyVec sys.A D.postSelectionGoodComponent =
      (inversionConstant sys.κ : ℂ) • (sys.b : HilbertVector R)
  rw [postSelectionGoodComponent_eq_scaled_inverse]
  rw [HilbertOperator.applyVec_smul]
  exact congrArg (fun v : HilbertVector R => (inversionConstant sys.κ : ℂ) • v)
    D.applyVec_inverseSolutionVec

/-- The post-selected good component points in the normalized solution direction. -/
public lemma postSelectionGoodComponent_eq_scaled_normalized (D : LinearSystem.SpectralData sys) :
    D.postSelectionGoodComponent =
      ((inversionConstant sys.κ : ℂ) * (‖D.inverseSolutionVec‖ : ℂ)) •
        (D.normalizedSolutionState : HilbertVector R) := by
  rw [postSelectionGoodComponent_eq_scaled_inverse]
  rw [normalizedSolutionState_coe]
  rw [smul_smul]
  have hnorm_pos : 0 < ‖D.inverseSolutionVec‖ :=
    norm_pos_iff.mpr D.inverseSolutionVec_ne_zero
  have hnorm : (‖D.inverseSolutionVec‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hnorm_pos)
  congr 1
  field_simp [hnorm]

/-- The direction of the nonzero spectral good component, certified to have norm one. -/
public noncomputable def postSelectionGoodState (D : LinearSystem.SpectralData sys) :
  NormalizedVector R :=
  NormalizedVector.ofNeZero D.postSelectionGoodComponent D.postSelectionGoodComponent_ne_zero

/-- Normalizing the positive scalar multiple yields the same solution direction. -/
public lemma postSelectionGoodState_eq_normalizedSolutionState (D : LinearSystem.SpectralData
  sys) :
    D.postSelectionGoodState = D.normalizedSolutionState := by
  apply NormalizedVector.ext
  intro i
  have hvec :
      ((‖D.postSelectionGoodComponent‖ : ℂ)⁻¹) • D.postSelectionGoodComponent =
        ((‖D.inverseSolutionVec‖ : ℂ)⁻¹) • D.inverseSolutionVec := by
    rw [postSelectionGoodComponent_eq_scaled_inverse]
    rw [smul_smul]
    have hC_pos : 0 < inversionConstant sys.κ :=
      one_div_pos.mpr (mul_pos (by norm_num) sys.hκ_pos)
    have hC_norm : ‖(inversionConstant sys.κ : ℂ)‖ = inversionConstant sys.κ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hC_pos)]
    have hvec : D.inverseSolutionVec ≠ 0 := D.inverseSolutionVec_ne_zero
    have hnorm_pos : 0 < ‖D.inverseSolutionVec‖ := norm_pos_iff.mpr hvec
    have hC_ne : (inversionConstant sys.κ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hC_pos)
    have hnorm_ne : (‖D.inverseSolutionVec‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hnorm_pos)
    have hpost_norm :
        ‖(inversionConstant sys.κ : ℂ) • D.inverseSolutionVec‖ =
          inversionConstant sys.κ * ‖D.inverseSolutionVec‖ := by
      rw [norm_smul, hC_norm]
    have hpost_norm_coe :
        (‖(inversionConstant sys.κ : ℂ) • D.inverseSolutionVec‖ : ℂ) =
          (inversionConstant sys.κ : ℂ) * (‖D.inverseSolutionVec‖ : ℂ) := by
      rw [hpost_norm, Complex.ofReal_mul]
    rw [hpost_norm_coe]
    congr 1
    field_simp [hC_ne, hnorm_ne]
  exact congrArg (fun v : HilbertVector R => v i) hvec

/-- A supplied finite eigenpair expansion determines a normalized inverse solution. -/
public lemma spectral_solution (D : LinearSystem.SpectralData sys) :
    WithLp.toLp 2 (sys.A.mulVec D.inverseSolutionVec.ofLp) = (sys.b : HilbertVector R) ∧
      D.postSelectionGoodState = D.normalizedSolutionState ∧
      (∀ j, |inversionConstant sys.κ / D.eigenvalue j| ≤ 1 / 2) :=
  ⟨D.applyVec_inverseSolutionVec, D.postSelectionGoodState_eq_normalizedSolutionState,
    fun j => D.inversionCoefficient_abs_le_half j⟩

end LinearSystem.SpectralData

/-- Twice the arcsine of the absolute-eigenvalue inversion coefficient. -/
public noncomputable def inversionAngle (eigenvalue κ : ℝ) : ℝ :=
  2 * Real.arcsin (inversionConstant κ / |eigenvalue|)

/-- The candidate ancilla coefficients as a scalar pair; normalization requires a separate
  amplitude bound. -/
public noncomputable def inversionAncillaCoeffs (eigenvalue κ : ℝ) : ℂ × ℂ :=
  let C := inversionConstant κ
  (Complex.ofReal (Real.sqrt (1 - (C / eigenvalue) ^ 2)),
   Complex.ofReal (C / eigenvalue))

/-- Nonnegativity of the squared inversion coefficient. -/
public lemma inversionSuccessProb_nonneg (eigenvalue κ : ℝ) (_hκ_pos : 0 < κ) :
    (inversionConstant κ / eigenvalue) ^ 2 ≥ 0 := sq_nonneg _

end QuantumAlg

end
