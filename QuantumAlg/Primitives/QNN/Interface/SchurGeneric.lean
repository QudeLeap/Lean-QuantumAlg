/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Interface.CasimirInvariant

/-!
# Generic `(g⊗g)^g` infrastructure toward the Schur hypothesis (H2)

This module provides the dimension-agnostic machinery for proving the Schur one-dimensionality
`(g⊗g)^g = span{C}` (the named hypothesis `invariant_eq_spanC` carried by the de-circularized Ragone
interface). It is split off from the concrete `su(2)` discharge so the reusable parts stay generic:

* `doubledAd_kron` — the doubled (coproduct) adjoint action on a Kronecker product splits as a
  Leibniz rule `doubledAd a (u ⊗ₖ v) = ⁅a, u⁆ ⊗ₖ v + u ⊗ₖ ⁅a, v⁆`.
* `hsInner_kron_basis` — the family `Bᵢ ⊗ₖ Bⱼ` is Hilbert–Schmidt orthonormal.
* `projGG_eq_self_of_mem` / `gTensorG_coord` — coefficient extraction: every `X ∈ g ⊗ g` is its own
  HS expansion `X = ∑ᵢⱼ ⟪Bᵢ⊗ₖBⱼ, X⟫ • (Bᵢ⊗ₖBⱼ)`.
* `spanC_le_gTensorGInvariant` — the easy half `span{C} ≤ (g⊗g)^g`.

The hard half (`(g⊗g)^g ≤ span{C}`) is the `su(2)`-specific solve, built on top of these.
-/

@[expose] public section

namespace QuantumAlg

open Matrix
open scoped Kronecker

attribute [local instance 100] LieRing.ofAssociativeRing

variable {N : ℕ} {gens : Set (Matrix (Fin N) (Fin N) ℂ)}

/-- The Hilbert–Schmidt inner product is zero against `0` on the right. -/
theorem hsInner_zero_right {m : Type*} [Fintype m] (A : Matrix m m ℂ) : hsInner A 0 = 0 := by
  simp [hsInner]

/-- **Leibniz rule for the doubled adjoint action on a Kronecker product.** The coproduct action
`doubledAd a = ⁅a⊗ₖ1 + 1⊗ₖa, ·⁆` differentiates across the tensor:
`doubledAd a (u ⊗ₖ v) = ⁅a, u⁆ ⊗ₖ v + u ⊗ₖ ⁅a, v⁆`. -/
theorem doubledAd_kron (a u v : Matrix (Fin N) (Fin N) ℂ) :
    doubledAd a (u ⊗ₖ v) = ⁅a, u⁆ ⊗ₖ v + u ⊗ₖ ⁅a, v⁆ := by
  simp only [doubledAd, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  rw [add_mul, mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, Ring.lie_def, sub_kron, kron_sub]
  abel

/-- **The doubled basis `Bᵢ ⊗ₖ Bⱼ` is Hilbert–Schmidt orthonormal.** -/
theorem hsInner_kron_basis (b : DLAHermBasis gens) (p q : Fin b.dim × Fin b.dim) :
    hsInner (b.B p.1 ⊗ₖ b.B p.2) (b.B q.1 ⊗ₖ b.B q.2) = if p = q then 1 else 0 := by
  rw [hsInner_kronecker, b.ortho, b.ortho]
  by_cases h : p = q
  · subst h; simp
  · rw [if_neg h, Prod.ext_iff, not_and_or] at *
    rcases h with h1 | h2
    · rw [if_neg h1, zero_mul]
    · rw [if_neg h2, mul_zero]

/-- **The HS projection onto `g ⊗ g` fixes `g ⊗ g`** (coefficient self-consistency). -/
theorem projGG_eq_self_of_mem (b : DLAHermBasis gens)
    {X : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ} (hX : X ∈ gTensorG b) :
    projGG b X = X := by
  rw [gTensorG] at hX
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hX
  have key : ∀ p : Fin b.dim × Fin b.dim,
      hsInner (b.B p.1 ⊗ₖ b.B p.2)
          (∑ q : Fin b.dim × Fin b.dim, c q • (b.B q.1 ⊗ₖ b.B q.2)) = c p := by
    intro p
    simp only [hsInner_sum_right, hsInner_smul_right, hsInner_kron_basis, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [projGG_apply]
  change ∑ p : Fin b.dim × Fin b.dim,
      hsInner (b.B p.1 ⊗ₖ b.B p.2) (∑ q : Fin b.dim × Fin b.dim, c q • (b.B q.1 ⊗ₖ b.B q.2))
        • (b.B p.1 ⊗ₖ b.B p.2)
      = ∑ q : Fin b.dim × Fin b.dim, c q • (b.B q.1 ⊗ₖ b.B q.2)
  simp only [key]

/-- **Coefficient extraction in `g ⊗ g`.** Every `X ∈ g ⊗ g` is its own Hilbert–Schmidt expansion
in the orthonormal family `Bᵢ ⊗ₖ Bⱼ`. -/
theorem gTensorG_coord (b : DLAHermBasis gens)
    {X : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ} (hX : X ∈ gTensorG b) :
    X = ∑ i : Fin b.dim, ∑ j : Fin b.dim,
      hsInner (b.B i ⊗ₖ b.B j) X • (b.B i ⊗ₖ b.B j) := by
  conv_lhs => rw [← projGG_eq_self_of_mem b hX, projGG_apply]
  rw [Fintype.sum_prod_type]

/-- **The easy half: `span{C} ≤ (g⊗g)^g`.** The Casimir is in the invariant subspace
(`casimir_mem_gTensorGInvariant`), hence so is its span. -/
theorem spanC_le_gTensorGInvariant (b : DLAHermBasis gens) :
    Submodule.span ℂ {b.casimir} ≤ gTensorGInvariant b :=
  Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (casimir_mem_gTensorGInvariant b))

/-- **Pairing the doubled action against the basis** (generic). For `X ∈ g ⊗ g` with coefficients
`cᵢⱼ = ⟪Bᵢ⊗ₖBⱼ, X⟫`, the Hilbert–Schmidt residual of `doubledAd Bₖ X` against `Bₐ ⊗ₖ Bᵦ` is a pair
of structure-constant contractions:
`⟪Bₐ⊗ₖBᵦ, doubledAd Bₖ X⟫ = ∑ᵢ sₖᵢₐ cᵢᵦ + ∑ⱼ sₖⱼᵦ cₐⱼ`, where `sₖᵢₐ = ⟪Bₐ, ⁅Bₖ,Bᵢ⁆⟫`. Combined with
`doubledAd Bₖ X = 0` this is the scalar invariance equation forcing `c` to commute with the adjoint
action. -/
theorem doubledAd_pairing (b : DLAHermBasis gens)
    {X : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ} (hX : X ∈ gTensorG b)
    (k a bb : Fin b.dim) :
    hsInner (b.B a ⊗ₖ b.B bb) (doubledAd (b.B k) X)
      = (∑ i, hsInner (b.B a) ⁅b.B k, b.B i⁆ * hsInner (b.B i ⊗ₖ b.B bb) X)
        + ∑ j, hsInner (b.B bb) ⁅b.B k, b.B j⁆ * hsInner (b.B a ⊗ₖ b.B j) X := by
  conv_lhs => rw [gTensorG_coord b hX]
  simp only [map_sum, map_smul, doubledAd_kron, hsInner_sum_right, hsInner_smul_right,
    hsInner_add_right, hsInner_kronecker, b.ortho, mul_add, mul_ite, mul_one, mul_zero,
    ite_mul, one_mul, zero_mul, Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ bb), mul_comm]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ a), mul_comm]

/-! ### Step 0: invariance as a commutator with the adjoint matrix -/

/-- The matrix of `ad(Bₖ)` in the Hermitian basis: `(Sₖ)_{a,i} = ⟪Bₐ, ⁅Bₖ, Bᵢ⁆⟫`. -/
noncomputable def adMatrix (b : DLAHermBasis gens) (k : Fin b.dim) :
    Matrix (Fin b.dim) (Fin b.dim) ℂ :=
  Matrix.of fun a i => hsInner (b.B a) ⁅b.B k, b.B i⁆

/-- The coefficient matrix of `X ∈ g ⊗ g`: `C_{a,c} = ⟪Bₐ ⊗ₖ B_c, X⟫`. -/
noncomputable def coeffMatrix (b : DLAHermBasis gens)
    (X : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) : Matrix (Fin b.dim) (Fin b.dim) ℂ :=
  Matrix.of fun a c => hsInner (b.B a ⊗ₖ b.B c) X

/-- Each adjoint matrix is antisymmetric (the Hilbert–Schmidt form is ad-invariant). -/
theorem adMatrix_antisymm (b : DLAHermBasis gens) (k a i : Fin b.dim) :
    adMatrix b k a i = - adMatrix b k i a := by
  simp only [adMatrix, Matrix.of_apply]
  exact hsInner_bracket_antisymm b k i a

/-- **Step 0 — the coefficient matrix of an invariant tensor commutes with every adjoint matrix.**
For `X ∈ (g⊗g)^g`, `Sₖ · C = C · Sₖ`, i.e. `C` is an endomorphism of the adjoint module. -/
theorem gTensorGInvariant_commute (b : DLAHermBasis gens)
    {X : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ} (hX : X ∈ gTensorGInvariant b) (k : Fin b.dim) :
    adMatrix b k * coeffMatrix b X = coeffMatrix b X * adMatrix b k := by
  have hmem : X ∈ gTensorG b := hX.2
  have hker : doubledAd (b.B k) X = 0 := by
    have hc : X ∈ adCommutantGG b := hX.1
    simp only [adCommutantGG, Submodule.mem_iInf, LinearMap.mem_ker] at hc
    exact hc k
  ext a bb
  have key : hsInner (b.B a ⊗ₖ b.B bb) (doubledAd (b.B k) X) = 0 := by
    rw [hker, hsInner_zero_right]
  rw [doubledAd_pairing b hmem k a bb] at key
  have hS1 : (∑ i, hsInner (b.B a) ⁅b.B k, b.B i⁆ * hsInner (b.B i ⊗ₖ b.B bb) X)
      = - ∑ j, hsInner (b.B bb) ⁅b.B k, b.B j⁆ * hsInner (b.B a ⊗ₖ b.B j) X :=
    eq_neg_of_add_eq_zero_left key
  simp only [Matrix.mul_apply, adMatrix, coeffMatrix, Matrix.of_apply]
  rw [hS1, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsInner_bracket_antisymm b k bb j]
  ring

/-! ### Steps 2–4: the structure-constant solver `(g⊗g)^g ≤ span{C}` -/

/-- **Step 2 — off-diagonal vanishing.** If each `adMatrix bₖ ²` is diagonal with eigenvalues `μ k`
that separate every pair of distinct indices, the coefficient matrix of an invariant tensor is
diagonal. (`adMatrix bₖ ²` is diagonal because the Pauli bracket is single-term;
`μ k` depends only on
the symplectic pairing, which is non-degenerate — so it separates.) -/
theorem coeffMatrix_offdiag_zero (b : DLAHermBasis gens)
    {X : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ} (hX : X ∈ gTensorGInvariant b)
    (μ : Fin b.dim → Fin b.dim → ℂ)
    (hdiag : ∀ k, adMatrix b k * adMatrix b k = Matrix.diagonal (μ k))
    (hsep : ∀ a a' : Fin b.dim, a ≠ a' → ∃ k, μ k a ≠ μ k a')
    {a a' : Fin b.dim} (ha : a ≠ a') : coeffMatrix b X a a' = 0 := by
  obtain ⟨k, hk⟩ := hsep a a' ha
  have hcomm := gTensorGInvariant_commute b hX k
  have hcomm2 : Matrix.diagonal (μ k) * coeffMatrix b X
      = coeffMatrix b X * Matrix.diagonal (μ k) := by
    rw [← hdiag k, Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, hcomm, Matrix.mul_assoc]
  have he := congrFun (congrFun hcomm2 a) a'
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at he
  have hz : coeffMatrix b X a a' * (μ k a - μ k a') = 0 := by
    rw [mul_sub, mul_comm (coeffMatrix b X a a') (μ k a), he]; ring
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hk)

/-- **Step 3 — diagonal constancy.** A diagonal invariant coefficient matrix has
all diagonal entries
equal, because `adMatrix bₖ x y ≠ 0` forces `C x x = C y y` and the adjoint-support graph is
connected (`hconn`). -/
theorem coeffMatrix_diag_const (b : DLAHermBasis gens)
    {X : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ} (hX : X ∈ gTensorGInvariant b)
    (hoff : ∀ a a' : Fin b.dim, a ≠ a' → coeffMatrix b X a a' = 0)
    (hconn : ∀ t : Fin b.dim → ℂ,
      (∀ x y : Fin b.dim, (∃ k, adMatrix b k x y ≠ 0) → t x = t y) → ∀ x y, t x = t y)
    (a a' : Fin b.dim) : coeffMatrix b X a a = coeffMatrix b X a' a' := by
  refine hconn (fun a => coeffMatrix b X a a) (fun x y hxy => ?_) a a'
  obtain ⟨k, hk⟩ := hxy
  have hcomm := gTensorGInvariant_commute b hX k
  have he := congrFun (congrFun hcomm x) y
  have hL : (adMatrix b k * coeffMatrix b X) x y = adMatrix b k x y * coeffMatrix b X y y := by
    rw [Matrix.mul_apply, Finset.sum_eq_single y
      (fun i _ hiy => by rw [hoff i y hiy, mul_zero])
      (fun h => absurd (Finset.mem_univ y) h)]
  have hR : (coeffMatrix b X * adMatrix b k) x y = coeffMatrix b X x x * adMatrix b k x y := by
    rw [Matrix.mul_apply, Finset.sum_eq_single x
      (fun j _ hjx => by rw [hoff x j (Ne.symm hjx), zero_mul])
      (fun h => absurd (Finset.mem_univ x) h)]
  rw [hL, hR] at he
  have hs : adMatrix b k x y * (coeffMatrix b X y y - coeffMatrix b X x x) = 0 := by
    rw [mul_sub, he]; ring
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_left hk)).symm

/-- **Step 4 — assembly.** A diagonal, constant-on-the-diagonal invariant tensor
is a multiple of the
Casimir, hence the hard inclusion `(g⊗g)^g ≤ span{C}`. -/
theorem gTensorGInvariant_le_spanC (b : DLAHermBasis gens)
    {X : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ} (hX : X ∈ gTensorGInvariant b)
    (hoff : ∀ a a' : Fin b.dim, a ≠ a' → coeffMatrix b X a a' = 0)
    (hconst : ∀ a a' : Fin b.dim, coeffMatrix b X a a = coeffMatrix b X a' a') :
    X ∈ Submodule.span ℂ {b.casimir} := by
  rcases isEmpty_or_nonempty (Fin b.dim) with he | hne
  · have hX0 : X = 0 := by rw [gTensorG_coord b hX.2]; simp [Finset.univ_eq_empty]
    rw [hX0]; exact Submodule.zero_mem _
  · obtain ⟨a₀⟩ := hne
    rw [Submodule.mem_span_singleton]
    refine ⟨hsInner (b.B a₀ ⊗ₖ b.B a₀) X, ?_⟩
    conv_rhs => rw [gTensorG_coord b hX.2]
    rw [show b.casimir = ∑ j, b.B j ⊗ₖ b.B j from rfl, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a (fun c _ hca => by
          rw [show hsInner (b.B a ⊗ₖ b.B c) X = 0 from hoff a c (Ne.symm hca), zero_smul])
        (fun h => absurd (Finset.mem_univ a) h),
      show hsInner (b.B a ⊗ₖ b.B a) X = hsInner (b.B a₀ ⊗ₖ b.B a₀) X from hconst a a₀]

end QuantumAlg
