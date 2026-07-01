/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Base
public import QuantumAlg.Primitives.QNN.DynamicalLieAlgebra
public import QuantumAlg.Primitives.QNN.LieAlgebraicBP
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
  i.e. `A = i H`), the dynamical Lie algebra is closed under the adjoint `star = (·)ᴴ`.
  This is what makes the Hilbert–Schmidt orthogonal complement / Hermitian basis
  behave, and underlies the reductive (`g ⊆ u(N)`) structure of the DLA.
* (next) the Hermitian Hilbert–Schmidt orthonormal basis of the DLA, the quadratic
  Casimir, the `g`-purity, and the contraction identities (`⟪C,C⟫ = dim g`,
  `⟪C, H⊗H⟫ = P_g(H)`).
-/

@[expose] public section

namespace QuantumAlg

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {N : ℕ}

/-- **The dynamical Lie algebra of skew-Hermitian generators is `*`-closed.** If every
generator `A` is skew-Hermitian (`star A = -A`, the physical case `A = i H` with `H`
Hermitian), then the adjoint `star x = xᴴ` of any element of the dynamical Lie algebra
is again in it. Hence the DLA is the complexification of a real Lie algebra inside
`u(N)`, and admits a Hilbert–Schmidt orthonormal basis of Hermitian matrices. -/
theorem dynamicalLieAlgebra_star_mem
    {gens : Set (Matrix (Fin N) (Fin N) ℂ)} (hskew : ∀ A ∈ gens, star A = -A)
    {x : Matrix (Fin N) (Fin N) ℂ} (hx : x ∈ dynamicalLieAlgebra gens) :
    star x ∈ dynamicalLieAlgebra gens := by
  refine LieSubalgebra.lieSpan_induction ℂ
    (p := fun t _ => star t ∈ dynamicalLieAlgebra gens) ?_ ?_ ?_ ?_ ?_ hx
  · -- generators: `star b = -b ∈ DLA`
    intro b hb
    simpa only [dynamicalLieAlgebra, hskew b hb] using
      neg_mem (LieSubalgebra.subset_lieSpan hb)
  · -- zero
    simp
  · -- addition
    intro a b _ _ ha hb
    simpa only [star_add] using add_mem ha hb
  · -- scalar multiplication
    intro c a _ ha
    simpa only [star_smul] using SMulMemClass.smul_mem (star c) ha
  · -- Lie bracket: `star ⁅a,b⁆ = -⁅star a, star b⁆ ∈ DLA`
    intro a b _ _ ha hb
    have h : star ⁅a, b⁆ = -⁅star a, star b⁆ := by
      simp only [Ring.lie_def, star_sub, star_mul]
      abel
    simpa only [h] using neg_mem (LieSubalgebra.lie_mem _ ha hb)

/-- Restated with the conjugate-transpose notation: the DLA of skew-Hermitian
generators is closed under `(·)ᴴ`. -/
theorem dynamicalLieAlgebra_conjTranspose_mem
    {gens : Set (Matrix (Fin N) (Fin N) ℂ)} (hskew : ∀ A ∈ gens, Aᴴ = -A)
    {x : Matrix (Fin N) (Fin N) ℂ} (hx : x ∈ dynamicalLieAlgebra gens) :
    xᴴ ∈ dynamicalLieAlgebra gens := by
  have := dynamicalLieAlgebra_star_mem (gens := gens)
    (by simpa only [star_eq_conjTranspose] using hskew) hx
  simpa only [star_eq_conjTranspose] using this

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

end DLAHermBasis

/-! ### The variance formula (simple-DLA case) from the Haar second-moment hypotheses

The deep analytic / representation-theoretic facts that are genuine Mathlib gaps — a
normalized Haar measure on the dynamical Lie group, the twirl-is-a-projector property
(Steps 3–4), the vanishing of the mean for a simple algebra (Step 5), and the
one-dimensionality of `(g⊗g)^G` (Step 7, Schur) — are bundled into the hypothesis
structure below. The closed-form value is then genuinely derived from the proved
Steps 9a/9b. The existence of the Hermitian orthonormal basis `DLAHermBasis` (for
skew-Hermitian generators the DLA is `*`-closed by `dynamicalLieAlgebra_star_mem`,
hence the complexification of its Hermitian real form `V_h = V ∩ selfAdjoint` with
`V = V_h ⊕ i·V_h`; a Frobenius-orthonormal basis of `V_h` is a Hermitian orthonormal
`ℂ`-basis of `V`) is a standard finite-dimensional linear-algebra fact, taken here as
input — it is not a deep gap like Haar/Schur. -/

/-- **Bundled Haar / representation-theoretic input** [RBS+23, Arxiv_Final.tex:1264, 1285],
simple-DLA case: the loss variance is the Hilbert–Schmidt pairing of `ρ⊗ρ` with the
second-moment operator `M²(O⊗O)`, and the latter is the orthogonal projection of `O⊗O`
onto the one-dimensional `G`-invariant space `span{C}` (the quadratic Casimir). -/
structure RagoneSecondMoment {gens : Set (Matrix (Fin N) (Fin N) ℂ)} (b : DLAHermBasis gens)
    (ρ O : Matrix (Fin N) (Fin N) ℂ) where
  /-- The loss-gradient variance. -/
  variance : ℝ
  /-- The second-moment (twirl) operator evaluated at `O ⊗ O`. -/
  secondMoment : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ
  /-- Step 2 (Haar second moment): `Var = ⟪ρ⊗ρ, M²(O⊗O)⟫`. The `variance` field is the Haar
  second moment of the loss, which equals the gradient variance in the source's centered
  (zero-mean) setting. -/
  var_eq : (variance : ℂ) = hsInner (ρ ⊗ₖ ρ) secondMoment
  /-- Steps 4–7: `M²(O⊗O)` lies in the one-dimensional invariant space `span{C}`. -/
  proj_mem : ∃ κ : ℂ, secondMoment = κ • b.casimir
  /-- Step 4 (orthogonal projection): residual `⊥ C`, i.e. `⟪C,O⊗O⟫ = ⟪C,M²(O⊗O)⟫`. -/
  proj_orth : hsInner b.casimir (O ⊗ₖ O) = hsInner b.casimir secondMoment

/-- **The Lie-algebraic loss-variance formula (simple-DLA case)** —
[RBS+23, Arxiv_Final.tex:691], the `k=1` case. Given the bundled Haar/twirl/Schur
hypotheses and Hermitian `ρ`, `O`, the loss variance is `P_g(ρ) · P_g(O) / dim(g)`.
Genuinely derived from the
proved Casimir identities (Steps 9a/9b); only the `RagoneSecondMoment` data is assumed. -/
theorem RagoneSecondMoment.variance_eq_gPurity {gens : Set (Matrix (Fin N) (Fin N) ℂ)}
    {b : DLAHermBasis gens} {ρ O : Matrix (Fin N) (Fin N) ℂ}
    (M : RagoneSecondMoment b ρ O) (hρ : ρᴴ = ρ) (hO : Oᴴ = O) (hdim : 0 < b.dim) :
    (M.variance : ℂ) = b.gPurity ρ * b.gPurity O / (b.dim : ℂ) := by
  obtain ⟨κ, hκ⟩ := M.proj_mem
  have hdim' : (b.dim : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hdim.ne'
  have hO2 : b.gPurity O = κ * (b.dim : ℂ) := by
    rw [← b.casimir_hsInner_kron hO, M.proj_orth, hκ, hsInner_smul_right, b.casimir_hsInner_self]
  have hρρ : (ρ ⊗ₖ ρ)ᴴ = ρ ⊗ₖ ρ := by rw [conjTranspose_kronecker, hρ]
  have hCρ : hsInner (ρ ⊗ₖ ρ) b.casimir = b.gPurity ρ := by
    rw [hsInner_comm_of_isHermitian hρρ b.casimir_isHermitian, b.casimir_hsInner_kron hρ]
  rw [M.var_eq, hκ, hsInner_smul_right, hCρ, hO2]
  field_simp

/-- **Non-vacuity: the bundle is satisfiable.** For any Hermitian orthonormal basis `b`
of a (nonzero-dimensional) dynamical Lie algebra and any Hermitian state `ρ` and
observable `O`, the `RagoneSecondMoment` hypotheses are simultaneously satisfiable —
witnessed by the rank-one second moment `(P_g(O)/dim) • C`. This shows the assumption
bundle is internally consistent, so `variance_eq_gPurity` is **not vacuously true**.
(It exhibits that the constraints are consistent; it does not construct the physical
Haar twirl, which remains the Mathlib gap.) -/
noncomputable def RagoneSecondMoment.ofHermitian {gens : Set (Matrix (Fin N) (Fin N) ℂ)}
    {b : DLAHermBasis gens} {ρ O : Matrix (Fin N) (Fin N) ℂ}
    (hρ : ρᴴ = ρ) (hO : Oᴴ = O) (hdim : 0 < b.dim) : RagoneSecondMoment b ρ O where
  variance := (b.gPurity ρ * b.gPurity O / (b.dim : ℂ)).re
  secondMoment := (b.gPurity O / (b.dim : ℂ)) • b.casimir
  var_eq := by
    have hρρ : (ρ ⊗ₖ ρ)ᴴ = ρ ⊗ₖ ρ := by rw [conjTranspose_kronecker, hρ]
    have hCρ : hsInner (ρ ⊗ₖ ρ) b.casimir = b.gPurity ρ := by
      rw [hsInner_comm_of_isHermitian hρρ b.casimir_isHermitian, b.casimir_hsInner_kron hρ]
    have hxr : (starRingEnd ℂ) (b.gPurity ρ * b.gPurity O / (b.dim : ℂ))
        = b.gPurity ρ * b.gPurity O / (b.dim : ℂ) := by
      rw [map_div₀, map_mul, b.gPurity_conj ρ, b.gPurity_conj O, map_natCast]
    rw [Complex.conj_eq_iff_re.mp hxr, hsInner_smul_right, hCρ]
    ring
  proj_mem := ⟨b.gPurity O / (b.dim : ℂ), rfl⟩
  proj_orth := by
    have hdim' : (b.dim : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hdim.ne'
    rw [hsInner_smul_right, b.casimir_hsInner_self, b.casimir_hsInner_kron hO]
    field_simp

/-! ### Reductive case: the Eq. (9) sum, DERIVED from the direct-sum decomposition `g = ⊕ⱼ gⱼ`

The dynamical Lie algebra of a reductive theory is the *orthogonal* direct sum `g = ⊕ⱼ gⱼ` of
its (simple + abelian) ideals [RBS+23, Arxiv_Final.tex:640]. We model this by a finite family of
components whose Hermitian
Hilbert–Schmidt orthonormal bases are **mutually orthogonal across components** — i.e. their
union is an orthonormal basis of `g = ⊕ⱼ gⱼ`. The Eq. (9) sum is then genuinely *derived*
(the earlier `total_eq` "the variance is the sum of per-component variances" is no longer an
assumption): the only assumed (Haar/Schur) input is that the second-moment operator projects
onto the invariant space spanned by the per-ideal Casimirs `{Cⱼ}`. -/

/-- **Reductive-case input** [RBS+23, Arxiv_Final.tex:674, 682] (Theorem 1 / Eq. (9)). The
orthogonal direct-sum decomposition `g = ⊕ⱼ gⱼ` together with the per-ideal second-moment
projection. -/
structure RagoneReductive (ρ O : Matrix (Fin N) (Fin N) ℂ) where
  /-- Number of ideals in `g = ⊕ⱼ gⱼ`. -/
  numComp : ℕ
  /-- Generators of each ideal. -/
  gens : Fin numComp → Set (Matrix (Fin N) (Fin N) ℂ)
  /-- A Hermitian orthonormal basis of each ideal. -/
  basis : (j : Fin numComp) → DLAHermBasis (gens j)
  /-- The bases are mutually Hilbert–Schmidt orthogonal across distinct ideals: their union is
  an orthonormal basis of the orthogonal direct sum `g = ⊕ⱼ gⱼ`. -/
  cross_ortho : ∀ i j, i ≠ j → ∀ a b, hsInner ((basis i).B a) ((basis j).B b) = 0
  /-- Total loss-gradient variance. -/
  variance : ℝ
  /-- The second-moment (twirl) operator at `O ⊗ O`. -/
  secondMoment : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ
  /-- Step 2 (Haar second moment): `Var = ⟪ρ⊗ρ, M²(O⊗O)⟫`. The `variance` field is the Haar
  second moment of the loss, which equals the gradient variance in the source's centered
  (zero-mean) setting. -/
  var_eq : (variance : ℂ) = hsInner (ρ ⊗ₖ ρ) secondMoment
  /-- Steps 4–7 (named Haar/Schur input): `M²(O⊗O) = Σⱼ κⱼ Cⱼ` lies in the invariant space
  spanned by the per-ideal Casimirs. -/
  proj_mem : ∃ κ : Fin numComp → ℂ, secondMoment = ∑ j, κ j • (basis j).casimir
  /-- Step 4 (orthogonal projection), per ideal: `⟪Cⱼ, O⊗O⟫ = ⟪Cⱼ, M²(O⊗O)⟫`. -/
  proj_orth : ∀ j, hsInner (basis j).casimir (O ⊗ₖ O) = hsInner (basis j).casimir secondMoment

namespace RagoneReductive

variable {ρ O : Matrix (Fin N) (Fin N) ℂ} (R : RagoneReductive ρ O)

/-- **Cross-ideal Casimir orthogonality.** `⟪Cᵢ, Cⱼ⟫ = δᵢⱼ · dim gᵢ`. The `i = j` case is
`casimir_hsInner_self`; the `i ≠ j` case follows from the cross-orthogonality of the bases. -/
theorem casimir_cross (i j : Fin R.numComp) :
    hsInner (R.basis i).casimir (R.basis j).casimir
      = if i = j then ((R.basis i).dim : ℂ) else 0 := by
  by_cases h : i = j
  · subst h; rw [if_pos rfl]; exact (R.basis i).casimir_hsInner_self
  · rw [if_neg h, DLAHermBasis.casimir, DLAHermBasis.casimir, hsInner_sum_left]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hsInner_sum_right]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [hsInner_kronecker, R.cross_ortho i j h a b, zero_mul]

/-- **Reductive-case variance formula — [RBS+23, Arxiv_Final.tex:682] (Eq. (9)), DERIVED.**
The total loss variance is the sum over the ideals of `g = ⊕ⱼ gⱼ` of
`P_{gⱼ}(ρ)·P_{gⱼ}(O)/dim(gⱼ)`. The
sum structure is *derived* from the orthogonal direct-sum decomposition (`casimir_cross`) and
the per-ideal second-moment projection — it is no longer an assumption. -/
theorem totalVariance_eq (hρ : ρᴴ = ρ) (hO : Oᴴ = O) (hdim : ∀ j, 0 < (R.basis j).dim) :
    (R.variance : ℂ)
      = ∑ j, (R.basis j).gPurity ρ * (R.basis j).gPurity O / ((R.basis j).dim : ℂ) := by
  obtain ⟨κ, hκ⟩ := R.proj_mem
  have hκj : ∀ j, κ j * ((R.basis j).dim : ℂ) = (R.basis j).gPurity O := by
    intro j
    have hpo := R.proj_orth j
    rw [(R.basis j).casimir_hsInner_kron hO, hκ, hsInner_sum_right] at hpo
    have hterm : ∀ i, hsInner (R.basis j).casimir (κ i • (R.basis i).casimir)
        = if j = i then κ i * ((R.basis j).dim : ℂ) else 0 := by
      intro i; rw [hsInner_smul_right, R.casimir_cross j i, mul_ite, mul_zero]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq] at hpo
    simpa using hpo.symm
  rw [R.var_eq, hκ, hsInner_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsInner_smul_right]
  have hρρ : (ρ ⊗ₖ ρ)ᴴ = ρ ⊗ₖ ρ := by rw [conjTranspose_kronecker, hρ]
  have hCρ : hsInner (ρ ⊗ₖ ρ) (R.basis i).casimir = (R.basis i).gPurity ρ := by
    rw [hsInner_comm_of_isHermitian hρρ (R.basis i).casimir_isHermitian,
      (R.basis i).casimir_hsInner_kron hρ]
  rw [hCρ]
  have hdimi : ((R.basis i).dim : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hdim i).ne'
  field_simp
  linear_combination (R.basis i).gPurity ρ * hκj i

end RagoneReductive

/-! ### Capstone: exponentially large DLA ⟹ barren plateau (genuine variance) -/

/-- **Capstone — the full chain circuit ⟹ DLA ⟹ dimension ⟹ variance ⟹ barren
plateau.** For a qubit-indexed family of simple-DLA circuits whose loss variance is the
genuine value `P_g(ρ)·P_g(O)/dim(g)` [RBS+23, Arxiv_Final.tex:691] (the `RagoneSecondMoment`
bundle), if the
`g`-purity numerator stays bounded and the dynamical Lie algebra dimension grows
exponentially in the qubit count, then the loss has a barren plateau. This consumes the
*proved* variance formula (`variance_eq_gPurity`) rather than an assumed variance law. -/
theorem ragone_hasBarrenPlateau {sz : ℕ → ℕ}
    {gens : (n : ℕ) → Set (Matrix (Fin (sz n)) (Fin (sz n)) ℂ)}
    {ρ O : (n : ℕ) → Matrix (Fin (sz n)) (Fin (sz n)) ℂ}
    {b : (n : ℕ) → DLAHermBasis (gens n)}
    (M : (n : ℕ) → RagoneSecondMoment (b n) (ρ n) (O n))
    (hρ : ∀ n, (ρ n)ᴴ = ρ n) (hO : ∀ n, (O n)ᴴ = O n) (hdimpos : ∀ n, 0 < (b n).dim)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, ‖(b n).gPurity (ρ n) * (b n).gPurity (O n)‖ ≤ C)
    {base : ℝ} (hbase : 1 < base) (hexp : ∀ n, base ^ n ≤ ((b n).dim : ℝ)) :
    HasBarrenPlateau (fun n => (M n).variance) := by
  refine ⟨base, hbase, C, hC, fun n => ?_⟩
  have hdimC : 0 < ((b n).dim : ℝ) := by exact_mod_cast hdimpos n
  have hbn : 0 < base ^ n := pow_pos (one_pos.trans hbase) n
  have hv : ((M n).variance : ℂ)
      = (b n).gPurity (ρ n) * (b n).gPurity (O n) / ((b n).dim : ℂ) :=
    (M n).variance_eq_gPurity (hρ n) (hO n) (hdimpos n)
  have hcast : |(M n).variance| = ‖((M n).variance : ℂ)‖ := (RCLike.norm_ofReal (K := ℂ) _).symm
  rw [sub_zero, hcast, hv, norm_div, RCLike.norm_natCast]
  exact div_le_div₀ hC (hbound n) hbn (hexp n)

/-! ### A concrete witness: the hypotheses are inhabited -/

/-- A concrete one-dimensional `DLAHermBasis`: the dynamical Lie algebra generated by
the identity, with the (already normalized) identity as its single Hermitian
orthonormal basis vector. Witnesses that the geometric hypotheses are inhabitable. -/
def trivialDLAHermBasis : DLAHermBasis ({1} : Set (Matrix (Fin 1) (Fin 1) ℂ)) where
  dim := 1
  B := fun _ => 1
  herm := fun _ => conjTranspose_one
  ortho := fun i j => by
    rw [Subsingleton.elim i j, if_pos rfl]
    simp [hsInner, conjTranspose_one, Matrix.trace_one]
  span_eq := by
    rw [Set.range_const, dynamicalLieAlgebra]
    exact (LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero
      (by rintro x rfl y rfl; exact lie_self _)).symm

/-- **The full hypothesis stack is non-vacuous.** There is a concrete dynamical Lie
algebra with a Hermitian orthonormal basis and a satisfiable second-moment bundle —
so the variance formula `variance_eq_gPurity` and the barren-plateau capstone are not
vacuously true. -/
theorem ragone_hypotheses_nonempty :
    ∃ (gens : Set (Matrix (Fin 1) (Fin 1) ℂ)) (b : DLAHermBasis gens)
      (ρ O : Matrix (Fin 1) (Fin 1) ℂ), Nonempty (RagoneSecondMoment b ρ O) :=
  ⟨_, trivialDLAHermBasis, 1, 1,
    ⟨RagoneSecondMoment.ofHermitian conjTranspose_one conjTranspose_one Nat.one_pos⟩⟩

/-- **The reductive hypothesis stack is non-vacuous.** A one-ideal instance of
`RagoneReductive` (built from the trivial DLA and its satisfiable second-moment bundle), so the
*derived* Eq. (9) sum `RagoneReductive.totalVariance_eq` is not vacuously true. -/
theorem ragone_reductive_nonempty :
    Nonempty (RagoneReductive (1 : Matrix (Fin 1) (Fin 1) ℂ) (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  let M := RagoneSecondMoment.ofHermitian (b := trivialDLAHermBasis)
    conjTranspose_one conjTranspose_one Nat.one_pos
  obtain ⟨κ, hκ⟩ := M.proj_mem
  exact ⟨{
    numComp := 1
    gens := fun _ => {1}
    basis := fun _ => trivialDLAHermBasis
    cross_ortho := fun i j hij => absurd (Subsingleton.elim i j) hij
    variance := M.variance
    secondMoment := M.secondMoment
    var_eq := M.var_eq
    proj_mem := ⟨fun _ => κ, by rw [Fin.sum_univ_one]; exact hκ⟩
    proj_orth := fun _ => M.proj_orth }⟩

end QuantumAlg
