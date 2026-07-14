/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Base
public import QuantumAlg.Primitives.QNN.Core.DynamicalLieAlgebra
public import QuantumAlg.Primitives.QNN.Core.LieAlgebraicBP
public import QuantumAlg.Util.HilbertSchmidt

/-!
# The Lie-algebraic loss-variance formula [RBS+23]: foundations

This module builds toward a genuine formalization of the loss-gradient variance law of
[RBS+23] (*A Lie algebraic theory of barren plateaus*, arXiv:2309.09342):
`Var_θ[ℓ] = P_g(ρ) · P_g(O) / dim(g)` for a simple dynamical Lie algebra `g`
(and the per-component sum for the reductive case). The deep analytic / representation-
theoretic inputs that are genuine Mathlib gaps (a normalized Haar measure on the
dynamical Lie group; the twirl-is-a-projector property; Schur's lemma for Lie modules /
`(g⊗g)^G` one-dimensional) are isolated as named hypotheses, while everything
downstream of them — the entire algebraic / Hilbert–Schmidt derivation of the closed
form — is machine-checked.

## Foundations (this file):

* **`*-closedness`** — when the circuit generators are skew-Hermitian (`star A = -A`,
  i.e. `A = i H`), the dynamical Lie algebra is closed under the adjoint `star = (·)ᴴ`
  and is the complexification of a real Lie algebra inside `u(N)`. This structural fact
  (`dynamicalLieAlgebra_star_mem` / `dynamicalLieAlgebra_conjTranspose_mem`, with the
  real-form dimension bridge `finrank_real_realForm_eq_finrank_complex_dla`) now lives in
  `QuantumAlg.Primitives.QNN.Core.DynamicalLieAlgebra`; it is what makes the Hilbert–Schmidt
  orthogonal complement / Hermitian basis behave, and underlies the reductive
  (`g ⊆ u(N)`) structure of the DLA.
* (next) the Hermitian Hilbert–Schmidt orthonormal basis of the DLA, the quadratic
  Casimir, the `g`-purity, and the contraction identities (`⟪C,C⟫ = dim g`,
  `⟪C, H⊗H⟫ = P_g(H)`).
-/

@[expose] public section

namespace QuantumAlg

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {N : ℕ}

/-! ### A Hermitian orthonormal basis of the DLA; the Casimir and the `g`-purity -/

open scoped Kronecker

/-- A **Hermitian Hilbert–Schmidt orthonormal basis** of the dynamical Lie algebra:
the data underlying the quadratic Casimir and the `g`-purity in [RBS+23].
Such a basis exists whenever the generators are skew-Hermitian (the DLA is then
`*`-closed, see `dynamicalLieAlgebra_star_mem`); existence is established separately. -/
structure DLAHermBasis (gens : Set (Matrix (Fin N) (Fin N) ℂ)) where
  /-- The number of basis elements (= `dim g`). -/
  dim : ℕ
  /-- The basis vectors. -/
  B : Fin dim → Matrix (Fin N) (Fin N) ℂ
  /-- Each basis vector is Hermitian (lies in `ig`). -/
  herm : ∀ j, (B j)ᴴ = B j
  /-- The basis is Hilbert–Schmidt orthonormal. -/
  ortho : ∀ i j, hsInner (B i) (B j) = if i = j then 1 else 0
  /-- The basis spans the dynamical Lie algebra. -/
  span_eq : Submodule.span ℂ (Set.range B) = (dynamicalLieAlgebra gens).toSubmodule

namespace DLAHermBasis

variable {gens : Set (Matrix (Fin N) (Fin N) ℂ)} (b : DLAHermBasis gens)

/-- For a Hermitian orthonormal basis, `Tr[Bᵢ Bₖ] = δᵢₖ`. -/
theorem trace_mul (i k : Fin b.dim) : (b.B i * b.B k).trace = if i = k then (1 : ℂ) else 0 := by
  have h := b.ortho i k
  rwa [hsInner, b.herm i] at h

/-- An orthonormal family is linearly independent. -/
theorem linearIndependent_B : LinearIndependent ℂ b.B := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have h1 : hsInner (b.B k) (∑ i, c i • b.B i) = c k := by
    rw [hsInner_sum_right]
    have hterm : ∀ i, hsInner (b.B k) (c i • b.B i) = if k = i then c i else 0 := by
      intro i
      rw [hsInner_smul_right, b.ortho k i]
      split <;> simp
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq]
    simp
  rw [hc] at h1
  simpa [hsInner] using h1.symm

/-- The basis cardinality is the dimension of the dynamical Lie algebra. -/
theorem dlaDim_eq : dlaDim gens = b.dim := by
  rw [dlaDim, ← b.span_eq, finrank_span_eq_card b.linearIndependent_B, Fintype.card_fin]

/-- The **quadratic Casimir** `C = Σⱼ Bⱼ ⊗ Bⱼ` (as a Kronecker product). -/
noncomputable def casimir : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ := ∑ j, b.B j ⊗ₖ b.B j

/-- The orthogonal projection of `H` onto the dynamical Lie algebra, `H_g = Σⱼ ⟪Bⱼ,H⟫ Bⱼ`. -/
noncomputable def gProj (H : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ∑ j, hsInner (b.B j) H • b.B j

/-- The **`g`-purity** `P_g(H) = Σⱼ |⟪Bⱼ,H⟫|²` [RBS+23, Arxiv_Final.tex:657]: a real,
nonnegative quantity (cast to `ℂ`). For Hermitian `H` it equals the bare Casimir
contraction `Σⱼ ⟪Bⱼ,H⟫²` (each `⟪Bⱼ,H⟫` is then real; see `casimir_hsInner_kron`) and
the `Tr[H_g²]` form (`gPurity_eq_trace`). -/
noncomputable def gPurity (H : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  ∑ i, (Complex.normSq (hsInner (b.B i) H) : ℂ)

/-- **Step 9a (normalization).** `⟪C, C⟫ = dim g` — the `1/dim(g)` factor. -/
theorem casimir_hsInner_self : hsInner b.casimir b.casimir = (b.dim : ℂ) := by
  rw [casimir, hsInner_sum_left]
  have hi : ∀ i, hsInner (b.B i ⊗ₖ b.B i) (∑ k, b.B k ⊗ₖ b.B k) = (1 : ℂ) := by
    intro i
    rw [hsInner_sum_right]
    have hk : ∀ k, hsInner (b.B i ⊗ₖ b.B i) (b.B k ⊗ₖ b.B k) = if i = k then (1 : ℂ) else 0 := by
      intro k
      rw [hsInner_kronecker, b.ortho i k]
      split <;> simp
    rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_ite_eq]
    simp
  rw [Finset.sum_congr rfl (fun i _ => hi i)]
  simp

/-- **Step 9b (contraction).** For Hermitian `H`, `⟪C, H ⊗ H⟫ = P_g(H)` — the Casimir
contracts to the `g`-purity. The bare contraction is `Σⱼ ⟪Bⱼ,H⟫²`; for Hermitian `H`
each `⟪Bⱼ,H⟫` is real, so it equals `Σⱼ |⟪Bⱼ,H⟫|² = P_g(H)`. -/
theorem casimir_hsInner_kron {H : Matrix (Fin N) (Fin N) ℂ} (hH : Hᴴ = H) :
    hsInner b.casimir (H ⊗ₖ H) = b.gPurity H := by
  rw [casimir, hsInner_sum_left, gPurity]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsInner_kronecker, ← Complex.mul_conj, hsInner_conj_of_isHermitian (b.herm i) hH]

/-- For Hermitian `H`, the `g`-purity coincides with the `Tr[H_g²]` form (`H_g = gProj H`),
[RBS+23, Arxiv_Final.tex:657]. -/
theorem gPurity_eq_trace {H : Matrix (Fin N) (Fin N) ℂ} (hH : Hᴴ = H) :
    b.gPurity H = (b.gProj H * b.gProj H).trace := by
  have key : (b.gProj H * b.gProj H).trace = ∑ i, (hsInner (b.B i) H) ^ 2 := by
    simp only [gProj, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, b.trace_mul, mul_ite, mul_one, mul_zero]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_ite_eq']
    simp [sq]
  rw [key, gPurity]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.mul_conj, hsInner_conj_of_isHermitian (b.herm i) hH, sq]

/-- The quadratic Casimir is Hermitian. -/
theorem casimir_isHermitian : b.casimirᴴ = b.casimir := by
  rw [casimir, conjTranspose_sum]
  exact Finset.sum_congr rfl fun j _ => by simp only [conjTranspose_kronecker, b.herm]

/-- The `g`-purity is real — it is a sum of squared norms. -/
theorem gPurity_conj (H : Matrix (Fin N) (Fin N) ℂ) :
    (starRingEnd ℂ) (b.gPurity H) = b.gPurity H := by
  rw [gPurity, map_sum]
  exact Finset.sum_congr rfl fun i _ => Complex.conj_ofReal _

/-- The `g`-purity of a basis element is `1` (it is normalized). -/
theorem gPurity_basis_elem (i : Fin b.dim) : b.gPurity (b.B i) = 1 := by
  rw [gPurity]
  have hterm : ∀ j, (Complex.normSq (hsInner (b.B j) (b.B i)) : ℂ)
      = if j = i then (1 : ℂ) else 0 := by
    intro j; rw [b.ortho j i]; split <;> simp
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite_eq']
  simp

/-- The `g`-purity is nonnegative: it is a sum of squared norms. -/
theorem gPurity_nonneg (H : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ (b.gPurity H).re := by
  rw [gPurity, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => by
    rw [Complex.ofReal_re]
    exact Complex.normSq_nonneg _

/-- The product of two `g`-purities is again a nonnegative real, cast to `ℂ`. -/
theorem gPurity_mul_gPurity_nonneg_real
    (H K : Matrix (Fin N) (Fin N) ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ b.gPurity H * b.gPurity K = (r : ℂ) := by
  refine ⟨(b.gPurity H).re * (b.gPurity K).re,
    mul_nonneg (b.gPurity_nonneg H) (b.gPurity_nonneg K), ?_⟩
  have hHim : (b.gPurity H).im = 0 := by
    have h := b.gPurity_conj H
    rwa [Complex.conj_eq_iff_im] at h
  have hKim : (b.gPurity K).im = 0 := by
    have h := b.gPurity_conj K
    rwa [Complex.conj_eq_iff_im] at h
  have hH : b.gPurity H = ((b.gPurity H).re : ℂ) := by
    apply Complex.ext <;> simp [hHim]
  have hK : b.gPurity K = ((b.gPurity K).re : ℂ) := by
    apply Complex.ext <;> simp [hKim]
  rw [hH, hK]
  simp

/-- The `g`-purity is a nonnegative real cast to `ℂ`, so its norm is its real part. -/
theorem norm_gPurity_eq_re (H : Matrix (Fin N) (Fin N) ℂ) :
    ‖b.gPurity H‖ = (b.gPurity H).re := by
  have him : (b.gPurity H).im = 0 := by
    have := b.gPurity_conj H
    rwa [Complex.conj_eq_iff_im] at this
  have hofRe : b.gPurity H = ((b.gPurity H).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hnorm : ‖b.gPurity H‖ = |(b.gPurity H).re| := by
    conv_lhs => rw [hofRe]
    exact RCLike.norm_ofReal (K := ℂ) _
  rw [hnorm, abs_of_nonneg (b.gPurity_nonneg H)]

/-- The orthogonal projection pairs to the purity on the left: `⟪H_g, H⟫ = P_g(H)`. -/
theorem hsInner_gProj_left (H : Matrix (Fin N) (Fin N) ℂ) :
    hsInner (b.gProj H) H = b.gPurity H := by
  rw [gProj, hsInner_sum_left, gPurity]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsInner_smul_left, ← Complex.normSq_eq_conj_mul_self]

/-- The orthogonal projection pairs to the purity on the right: `⟪H, H_g⟫ = P_g(H)`. -/
theorem hsInner_gProj_right (H : Matrix (Fin N) (Fin N) ℂ) :
    hsInner H (b.gProj H) = b.gPurity H := by
  rw [hsInner_conj_symm, b.hsInner_gProj_left, b.gPurity_conj]

/-- The orthogonal projection is idempotent under the inner product: `⟪H_g, H_g⟫ = P_g(H)`. -/
theorem hsInner_gProj_self (H : Matrix (Fin N) (Fin N) ℂ) :
    hsInner (b.gProj H) (b.gProj H) = b.gPurity H := by
  have hj : ∀ j, hsInner (b.B j) (b.gProj H) = hsInner (b.B j) H := by
    intro j
    rw [gProj, hsInner_sum_right]
    have hterm : ∀ k, hsInner (b.B j) (hsInner (b.B k) H • b.B k)
        = if j = k then hsInner (b.B k) H else 0 := by
      intro k
      rw [hsInner_smul_right, b.ortho j k, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_ite_eq]
    simp
  nth_rewrite 1 [gProj]
  rw [hsInner_sum_left, gPurity]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsInner_smul_left, hj j, ← Complex.normSq_eq_conj_mul_self]

/-- Bessel / Parseval inequality for the DLA basis. The `g`-purity is bounded by the
squared Hilbert-Schmidt norm, `P_g(H) ≤ Tr[Hᴴ H]`. -/
theorem gPurity_le_normSq (H : Matrix (Fin N) (Fin N) ℂ) :
    (b.gPurity H).re ≤ (hsInner H H).re := by
  have hsub : hsInner (H - b.gProj H) (H - b.gProj H) = hsInner H H - b.gPurity H := by
    rw [hsInner_sub_left, hsInner_sub_right, hsInner_sub_right,
      b.hsInner_gProj_left, b.hsInner_gProj_right, b.hsInner_gProj_self]
    ring
  have hge : 0 ≤ (hsInner (H - b.gProj H) (H - b.gProj H)).re :=
    hsInner_self_re_nonneg _
  rw [hsub, Complex.sub_re] at hge
  linarith

end DLAHermBasis

end QuantumAlg
