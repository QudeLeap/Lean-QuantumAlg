/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Complex.BigOperators

/-!
# The Quantum Fisher Information Matrix (QFIM), generator/covariance form

For a parameterized pure state `|ψ(θ)⟩` the **Quantum Fisher Information Matrix** is the real
symmetric PSD matrix `F` whose closed form, for the periodic ansatz `U(θ) = ∏ exp(-iθₖHₖ)`, is the
covariance matrix of the (Heisenberg-rotated) generators `hₐ` in the reference state `|ψ⟩`
[LJG+21, Eq. (QFIM-elements)]:
`[F]_{ab} = 4 ( Re⟨ψ|hₐh_b|ψ⟩ − ⟨ψ|hₐ|ψ⟩⟨ψ|h_b|ψ⟩ )`.

This file records the **quantum-free linear algebra** of that closed form over raw
matrices and a state
vector `ψ : n → ℂ`: the expectation `expval`, the quantum covariance `qCov`, the
matrix `qfim`, and its
basic properties — symmetry, positive-semidefiniteness, the Gram rank bound, and reparameterization.
The generator-covariance form is the definition used in this module.  The analytic
identification with the
fidelity second-order expansion / Fubini--Study metric is not hidden in this
definition; it is carried by
the explicit bridge data in `QuantumAlg.Util.QuantumFisher.FSBridge`.
-/

@[expose] public section

namespace QuantumAlg

open Matrix

variable {n : Type*} [Fintype n] {M : ℕ}

/-- The **expectation value** `⟨ψ|A|ψ⟩` of an operator `A` in the (unit) state `ψ`. -/
def expval (ψ : n → ℂ) (A : Matrix n n ℂ) : ℂ := star ψ ⬝ᵥ A *ᵥ ψ

theorem expval_def (ψ : n → ℂ) (A : Matrix n n ℂ) : expval ψ A = star ψ ⬝ᵥ A *ᵥ ψ := rfl

/-- **Adjoint relation:** `⟨ψ|Aᴴ|ψ⟩ = conj ⟨ψ|A|ψ⟩`. -/
theorem expval_conjTranspose (ψ : n → ℂ) (A : Matrix n n ℂ) :
    expval ψ Aᴴ = starRingEnd ℂ (expval ψ A) := by
  simp only [expval_def, starRingEnd_apply]
  rw [mulVec_conjTranspose, dotProduct_star, star_star, ← dotProduct_mulVec]

/-- For a Hermitian operator, the expectation value is its own conjugate (i.e. real). -/
theorem expval_conj_self_of_isHermitian {ψ : n → ℂ} {A : Matrix n n ℂ} (hA : Aᴴ = A) :
    starRingEnd ℂ (expval ψ A) = expval ψ A := by
  rw [← expval_conjTranspose, hA]

/-- The **quantum covariance** `Cov_ψ(A,B) = Re⟨ψ|AB|ψ⟩ − Re⟨ψ|A|ψ⟩·Re⟨ψ|B|ψ⟩`. -/
def qCov (ψ : n → ℂ) (A B : Matrix n n ℂ) : ℝ :=
  (expval ψ (A * B)).re - (expval ψ A).re * (expval ψ B).re

/-- The covariance is symmetric on Hermitian operators: `Cov_ψ(A,B) = Cov_ψ(B,A)`. -/
theorem qCov_comm {ψ : n → ℂ} {A B : Matrix n n ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B) :
    qCov ψ A B = qCov ψ B A := by
  have h : (expval ψ (A * B)).re = (expval ψ (B * A)).re := by
    have hBA : B * A = (A * B)ᴴ := by rw [conjTranspose_mul, hA, hB]
    rw [hBA, expval_conjTranspose, Complex.conj_re]
  simp only [qCov]
  rw [h]; ring

/-- The **Quantum Fisher Information Matrix** `[F]_{ab} = 4·Cov_ψ(hₐ, h_b)`. -/
def qfim (ψ : n → ℂ) (h : Fin M → Matrix n n ℂ) : Matrix (Fin M) (Fin M) ℝ :=
  Matrix.of fun a b => 4 * qCov ψ (h a) (h b)

theorem qfim_apply (ψ : n → ℂ) (h : Fin M → Matrix n n ℂ) (a b : Fin M) :
    qfim ψ h a b = 4 * qCov ψ (h a) (h b) := rfl

/-- **Symmetry of the QFIM** (for Hermitian generators). -/
theorem qfim_isSymm {ψ : n → ℂ} {h : Fin M → Matrix n n ℂ} (hh : ∀ a, (h a)ᴴ = h a) :
    (qfim ψ h).IsSymm := by
  change (qfim ψ h)ᵀ = qfim ψ h
  ext a b
  simp only [Matrix.transpose_apply, qfim_apply]
  rw [qCov_comm (hh b) (hh a)]

/-- The **centered state** `(A − ⟨A⟩)|ψ⟩`. The QFIM is the real Gram matrix of these vectors. -/
def centered (ψ : n → ℂ) (A : Matrix n n ℂ) : n → ℂ := A *ᵥ ψ - (expval ψ A) • ψ

/-- **The covariance is the inner product of centered states.** For Hermitian `A` and a unit state,
`⟪(A−⟨A⟩)ψ, (B−⟨B⟩)ψ⟫ = ⟨AB⟩ − ⟨A⟩⟨B⟩`. -/
theorem centered_inner {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) {A B : Matrix n n ℂ} (hA : Aᴴ = A) :
    star (centered ψ A) ⬝ᵥ centered ψ B = expval ψ (A * B) - expval ψ A * expval ψ B := by
  have e1 : star (A *ᵥ ψ) ⬝ᵥ (B *ᵥ ψ) = expval ψ (A * B) := by
    rw [expval_def, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hA]
  have e2 : star (A *ᵥ ψ) ⬝ᵥ ψ = expval ψ A := by
    rw [expval_def, star_mulVec, ← dotProduct_mulVec, hA]
  have e3 : star ψ ⬝ᵥ (B *ᵥ ψ) = expval ψ B := rfl
  simp only [centered, star_sub, star_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, e1, e2, e3, hψ, mul_one]
  ring

/-- **The covariance equals the real part of the centered-state inner product.** -/
theorem qCov_eq_inner_re {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) {A B : Matrix n n ℂ} (hA : Aᴴ = A) :
    qCov ψ A B = (star (centered ψ A) ⬝ᵥ centered ψ B).re := by
  have hAim : (expval ψ A).im = 0 :=
    Complex.conj_eq_iff_im.mp (expval_conj_self_of_isHermitian hA)
  simp only [qCov]
  rw [centered_inner hψ hA, Complex.sub_re, Complex.mul_re, hAim, zero_mul, sub_zero]

/-- `0 ≤ Re⟪w, w⟫` for any vector `w`. -/
private theorem re_dotProduct_star_self_nonneg (w : n → ℂ) : 0 ≤ (star w ⬝ᵥ w).re := by
  rw [dotProduct, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-- **Positive-semidefiniteness of the QFIM** (Hermitian generators, unit state).
The QFIM is the real
Gram matrix `4·Re⟪cₐ, c_b⟫` of the centered states, hence PSD. -/
theorem qfim_posSemidef {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    {h : Fin M → Matrix n n ℂ} (hh : ∀ a, (h a)ᴴ = h a) :
    (qfim ψ h).PosSemidef := by
  have hherm : (qfim ψ h).IsHermitian := by
    have hs := qfim_isSymm (ψ := ψ) hh
    ext i j
    simpa [Matrix.conjTranspose_apply, star_trivial, Matrix.transpose_apply]
      using congrFun (congrFun hs i) j
  refine (posSemidef_iff_dotProduct_mulVec).mpr ⟨hherm, fun x => ?_⟩
  set W : n → ℂ := ∑ a, (x a : ℂ) • centered ψ (h a) with hW
  have hbil : star W ⬝ᵥ W
      = ∑ a, ∑ b, ((x a : ℂ) * (x b : ℂ)) *
          (star (centered ψ (h a)) ⬝ᵥ centered ψ (h b)) := by
    rw [hW, star_sum, sum_dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [star_smul, smul_dotProduct, dotProduct_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  have hmv : ∀ a, (qfim ψ h *ᵥ x) a = ∑ b, (4 * qCov ψ (h a) (h b)) * x b := by
    intro a
    simp only [Matrix.mulVec, dotProduct, qfim_apply]
  have hLHS : star x ⬝ᵥ (qfim ψ h) *ᵥ x
      = ∑ a, ∑ b, (x a * x b) * (4 * (star (centered ψ (h a)) ⬝ᵥ centered ψ (h b)).re) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.star_apply, star_trivial, hmv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [qCov_eq_inner_re hψ (hh a)]
    ring
  have key : star x ⬝ᵥ (qfim ψ h) *ᵥ x = 4 * (star W ⬝ᵥ W).re := by
    rw [hLHS, hbil, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [key]
  have hnn := re_dotProduct_star_self_nonneg W
  positivity

/-! ### Bilinearity of the covariance and the Gram-factorization rank bound

To avoid the (uncached) real-module structure on `Matrix n n ℂ`, real coefficients are carried as
`(c : ℝ)` cast to `ℂ` and the scalar action is the ambient `ℂ`-`smul`. -/

theorem expval_add (ψ : n → ℂ) (A B : Matrix n n ℂ) :
    expval ψ (A + B) = expval ψ A + expval ψ B := by
  rw [expval, expval, expval, add_mulVec, dotProduct_add]

theorem expval_smul (ψ : n → ℂ) (d : ℂ) (A : Matrix n n ℂ) :
    expval ψ (d • A) = d • expval ψ A := by
  rw [expval, expval, smul_mulVec, dotProduct_smul]

theorem expval_zero (ψ : n → ℂ) : expval ψ 0 = 0 := by
  rw [expval, zero_mulVec, dotProduct_zero]

theorem qCov_zero_left (ψ : n → ℂ) (B : Matrix n n ℂ) : qCov ψ 0 B = 0 := by
  simp only [qCov, zero_mul, expval_zero, Complex.zero_re, zero_mul, sub_zero]

theorem qCov_zero_right (ψ : n → ℂ) (A : Matrix n n ℂ) : qCov ψ A 0 = 0 := by
  simp only [qCov, mul_zero, expval_zero, Complex.zero_re, mul_zero, sub_zero]

theorem qCov_add_left (ψ : n → ℂ) (A A' B : Matrix n n ℂ) :
    qCov ψ (A + A') B = qCov ψ A B + qCov ψ A' B := by
  simp only [qCov, add_mul, expval_add, Complex.add_re]; ring

theorem qCov_add_right (ψ : n → ℂ) (A B B' : Matrix n n ℂ) :
    qCov ψ A (B + B') = qCov ψ A B + qCov ψ A B' := by
  simp only [qCov, mul_add, expval_add, Complex.add_re]; ring

theorem qCov_ofReal_smul_left (ψ : n → ℂ) (c : ℝ) (A B : Matrix n n ℂ) :
    qCov ψ ((c : ℂ) • A) B = c * qCov ψ A B := by
  simp only [qCov, smul_mul_assoc, expval_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]; ring

theorem qCov_ofReal_smul_right (ψ : n → ℂ) (c : ℝ) (A B : Matrix n n ℂ) :
    qCov ψ A ((c : ℂ) • B) = c * qCov ψ A B := by
  simp only [qCov, mul_smul_comm, expval_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]; ring

theorem qCov_sum_ofReal_smul_left (ψ : n → ℂ) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (g : ι → Matrix n n ℂ) (B : Matrix n n ℂ) :
    qCov ψ (∑ j ∈ s, (c j : ℂ) • g j) B = ∑ j ∈ s, c j * qCov ψ (g j) B := by
  classical
  induction s using Finset.induction with
  | empty => simp [qCov_zero_left]
  | insert _ _ hns ih =>
    rw [Finset.sum_insert hns, Finset.sum_insert hns, qCov_add_left, qCov_ofReal_smul_left, ih]

theorem qCov_sum_ofReal_smul_right (ψ : n → ℂ) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (g : ι → Matrix n n ℂ) (A : Matrix n n ℂ) :
    qCov ψ A (∑ j ∈ s, (c j : ℂ) • g j) = ∑ j ∈ s, c j * qCov ψ A (g j) := by
  classical
  induction s using Finset.induction with
  | empty => simp [qCov_zero_right]
  | insert _ _ hns ih =>
    rw [Finset.sum_insert hns, Finset.sum_insert hns, qCov_add_right, qCov_ofReal_smul_right, ih]

/-- **Reparameterization covariance** (a QFIM basic property). Under a real-linear
reparameterization of
the generators `hᵢ' = ∑ₐ Jᵢₐ hₐ`, the QFIM transforms covariantly: `F' = J · F · Jᵀ`. -/
theorem qfim_reparam {M' : ℕ} (ψ : n → ℂ) (h : Fin M → Matrix n n ℂ)
    (J : Matrix (Fin M') (Fin M) ℝ) :
    qfim ψ (fun i => ∑ a, (J i a : ℂ) • h a) = J * qfim ψ h * Jᵀ := by
  ext i i'
  have hLi : qfim ψ (fun i => ∑ a, (J i a : ℂ) • h a) i i'
      = ∑ a, ∑ b, J i a * J i' b * qfim ψ h a b := by
    simp only [qfim_apply]
    rw [qCov_sum_ofReal_smul_left, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [qCov_sum_ofReal_smul_right, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hLi]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- **Gram-factorization rank bound.** If every generator `hₐ` is a *real* linear combination of a
family `g` of `d` operators, then `rank(F) ≤ d`. (For the DLA case `g` is the Hermitian basis,
`d = dim g`.) Via reparameterization covariance `F = R · (qfim ψ g) · Rᵀ`. -/
theorem qfim_rank_le_of_real_combo {d : ℕ} (ψ : n → ℂ) {h : Fin M → Matrix n n ℂ}
    (g : Fin d → Matrix n n ℂ) (hcombo : ∀ a, ∃ r : Fin d → ℝ, h a = ∑ j, (r j : ℂ) • g j) :
    (qfim ψ h).rank ≤ d := by
  choose r hr using hcombo
  have hh : h = fun i => ∑ j, ((Matrix.of r i j : ℝ) : ℂ) • g j := by
    funext i; exact hr i
  rw [hh, qfim_reparam, Matrix.mul_assoc]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin d))

end QuantumAlg
