/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic

/-!
# Fourier expansion of an exponentially conjugated Hermitian matrix

The spectral theorem gives an exact finite Fourier expansion of
`ψ† exp(ixG)† O exp(ixG) ψ`, with frequencies the eigenvalue differences of `G`.
The double sum includes all equal-eigenvalue pairs; degeneracies therefore contribute
their off-diagonal matrix entries to the constant coefficient as well.
This is finite-dimensional matrix algebra and does not assume a quantum execution.
-/

@[expose] public section

namespace Matrix

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinates of a vector in the orthonormal eigenbasis of a Hermitian matrix. -/
def spectralCoordinates {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (ψ : ι → ℂ) : ι → ℂ :=
  (hG.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ ψ

/-- The observable expressed in the eigenbasis of the generator. -/
def spectralObservable {G : Matrix ι ι ℂ} (hG : G.IsHermitian)
    (O : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (hG.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * O * hG.eigenvectorUnitary

/-- The coefficient belonging to an ordered pair of generator eigenvectors. -/
def spectralExpectationCoeff {G : Matrix ι ι ℂ} (hG : G.IsHermitian)
    (O : Matrix ι ι ℂ) (ψ : ι → ℂ) (i j : ι) : ℂ :=
  star (spectralCoordinates hG ψ i) * spectralObservable hG O i j *
    spectralCoordinates hG ψ j

/-- The actual matrix exponential is diagonal in the generator's eigenbasis. -/
lemma hermitian_exponential_spectral {G : Matrix ι ι ℂ}
    (hG : G.IsHermitian) (x : ℝ) :
    NormedSpace.exp (((x : ℂ) * Complex.I) • G) =
      (hG.eigenvectorUnitary : Matrix ι ι ℂ) *
        diagonal (fun i => Complex.exp (((hG.eigenvalues i * x : ℝ) : ℂ) * Complex.I)) *
          (hG.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  let V := hG.eigenvectorUnitary
  let D : Matrix ι ι ℂ := diagonal (fun i => (hG.eigenvalues i : ℂ))
  have hdiag : G = (V : Matrix ι ι ℂ) * D * (V : Matrix ι ι ℂ)ᴴ := by
    simpa [V, D, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
      Function.comp_def] using hG.spectral_theorem
  have hconj := Matrix.exp_units_conj (Unitary.toUnits V)
    (((x : ℂ) * Complex.I) • D)
  have hconj' :
      NormedSpace.exp ((V : Matrix ι ι ℂ) * (((x : ℂ) * Complex.I) • D) *
          (V : Matrix ι ι ℂ)ᴴ) =
        (V : Matrix ι ι ℂ) * NormedSpace.exp (((x : ℂ) * Complex.I) • D) *
          (V : Matrix ι ι ℂ)ᴴ := by
    exact hconj
  have harg : ((x : ℂ) * Complex.I) • G =
      (V : Matrix ι ι ℂ) * (((x : ℂ) * Complex.I) • D) * (V : Matrix ι ι ℂ)ᴴ := by
    calc
      _ = ((x : ℂ) * Complex.I) • ((V : Matrix ι ι ℂ) * D *
          (V : Matrix ι ι ℂ)ᴴ) := congrArg (fun A => ((x : ℂ) * Complex.I) • A) hdiag
      _ = _ := by rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [harg, hconj']
  congr 2
  dsimp only [D]
  rw [← diagonal_smul, exp_diagonal]
  congr 1
  funext i
  simp only [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
  congr 1
  push_cast
  ring

omit [DecidableEq ι] in
private lemma expectation_conjugate (U O : Matrix ι ι ℂ) (ψ : ι → ℂ) :
    star ψ ⬝ᵥ ((Uᴴ * O * U) *ᵥ ψ) =
      star (U *ᵥ ψ) ⬝ᵥ (O *ᵥ (U *ᵥ ψ)) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

private lemma scalar_phase_pair (a b x : ℝ) :
    star (Complex.exp (((a * x : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((b * x : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((((b - a) * x : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Exact Fourier expansion of the matrix-exponential expectation.
No condition on the observable is needed for the complex-valued identity. -/
lemma hermitian_exponential_expectation_fourier {G : Matrix ι ι ℂ}
    (hG : G.IsHermitian) (O : Matrix ι ι ℂ) (ψ : ι → ℂ) (x : ℝ) :
    let U := NormedSpace.exp (((x : ℂ) * Complex.I) • G)
    star ψ ⬝ᵥ ((Uᴴ * O * U) *ᵥ ψ) =
      ∑ i, ∑ j, spectralExpectationCoeff hG O ψ i j *
        Complex.exp ((((hG.eigenvalues j - hG.eigenvalues i) * x : ℝ) : ℂ) * Complex.I) := by
  dsimp only
  let V : Matrix ι ι ℂ := hG.eigenvectorUnitary
  let D : Matrix ι ι ℂ :=
    diagonal (fun i => Complex.exp (((hG.eigenvalues i * x : ℝ) : ℂ) * Complex.I))
  let q := spectralCoordinates hG ψ
  let B := spectralObservable hG O
  rw [expectation_conjugate, hermitian_exponential_spectral hG]
  change star ((V * D * Vᴴ) *ᵥ ψ) ⬝ᵥ (O *ᵥ ((V * D * Vᴴ) *ᵥ ψ)) = _
  have hvec : (V * D * Vᴴ) *ᵥ ψ = V *ᵥ (D *ᵥ q) := by
    simp only [q, spectralCoordinates, V, mulVec_mulVec, Matrix.mul_assoc]
  rw [hvec, ← expectation_conjugate]
  change star (D *ᵥ q) ⬝ᵥ (B *ᵥ (D *ᵥ q)) = _
  change (∑ i, star (D *ᵥ q) i * ∑ j, B i j * (D *ᵥ q) j) = _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change star (D *ᵥ q) i * (B i j * (D *ᵥ q) j) = _
  simp only [Pi.star_apply, D, mulVec_diagonal, star_mul]
  rw [show star (q i) *
      star (Complex.exp (((hG.eigenvalues i * x : ℝ) : ℂ) * Complex.I)) *
        (B i j * (Complex.exp (((hG.eigenvalues j * x : ℝ) : ℂ) * Complex.I) * q j)) =
      (star (q i) * B i j * q j) *
        (star (Complex.exp (((hG.eigenvalues i * x : ℝ) : ℂ) * Complex.I)) *
          Complex.exp (((hG.eigenvalues j * x : ℝ) : ℂ) * Complex.I)) by ring]
  rw [scalar_phase_pair]
  rfl

/-- Hermitian observables have conjugate coefficients at opposite frequency pairs. -/
lemma hermitian_exponential_expectation_coeff_star {G O : Matrix ι ι ℂ}
    (hG : G.IsHermitian) (hO : O.IsHermitian) (ψ : ι → ℂ) (i j : ι) :
    star (spectralExpectationCoeff hG O ψ i j) =
      spectralExpectationCoeff hG O ψ j i := by
  have hB : (spectralObservable hG O).IsHermitian :=
    isHermitian_conjTranspose_mul_mul _ hO
  have hij : star (spectralObservable hG O i j) = spectralObservable hG O j i :=
    congrArg (fun M : Matrix ι ι ℂ => M j i) hB
  simp only [spectralExpectationCoeff, star_mul, star_star, hij]
  ring

/-- The expectation of a Hermitian observable is real, including after exponential conjugation. -/
lemma hermitian_exponential_expectation_real {G O : Matrix ι ι ℂ}
    (hO : O.IsHermitian) (ψ : ι → ℂ) (x : ℝ) :
    let U := NormedSpace.exp (((x : ℂ) * Complex.I) • G)
    (star ψ ⬝ᵥ ((Uᴴ * O * U) *ᵥ ψ)).im = 0 := by
  dsimp only
  let A :=
    (NormedSpace.exp (((x : ℂ) * Complex.I) • G))ᴴ * O *
      NormedSpace.exp (((x : ℂ) * Complex.I) • G)
  have hA : A.IsHermitian := isHermitian_conjTranspose_mul_mul _ hO
  change (star ψ ⬝ᵥ (A *ᵥ ψ)).im = 0
  apply Complex.conj_eq_iff_im.mp
  change star (star ψ ⬝ᵥ (A *ᵥ ψ)) = _
  have hadjoint : star ψ ⬝ᵥ (Aᴴ *ᵥ ψ) = star (star ψ ⬝ᵥ (A *ᵥ ψ)) := by
    rw [mulVec_conjTranspose, dotProduct_star, star_star, ← dotProduct_mulVec]
  rw [hA] at hadjoint
  exact hadjoint.symm

end

end Matrix
