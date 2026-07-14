/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Interface.CasimirInvariant

/-!
# The Lie-algebraic loss second-moment formula [RBS+23]: the non-circular interface

This module states the [RBS+23] loss second-moment interface as a bundle of NAMED, non-circular
hypotheses and derives the closed form `M₂ = P_g(ρ) · P_g(O) / dim(g)` (simple case) and the
per-ideal Eq. (9) sum (reductive case). In applications where a separate first-moment result proves
zero loss mean, this second moment is the corresponding loss variance. The second-moment (twirl)
operator is constrained to lie
in the genuine `g`-restricted invariant space `(g⊗g)^g = gTensorGInvariant` (built in `AdModule`),
whose key inhabitant — the quadratic Casimir — is supplied by `casimir_mem_adCommutantGG`
(`CasimirInvariant`). The one-dimensionality `(g⊗g)^g = span{C}` (Schur) and the finite-`2`-design
realization of the twirl remain isolated named hypotheses, as does the reductive case's
cross-ideal invariant-block exclusion; they are not posited to equal the answer.

The algebraic foundations (the Hermitian Hilbert–Schmidt basis, the quadratic Casimir, the
`g`-purity and the Casimir contraction identities) live in `VarianceFormula`.
-/

@[expose] public section

namespace QuantumAlg

open Matrix
open scoped Kronecker

attribute [local instance 100] LieRing.ofAssociativeRing

variable {N : ℕ}

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
simple-DLA case, stated against the genuine `g`-restricted invariant space. The loss second moment
is the Hilbert–Schmidt pairing of `ρ⊗ρ` with the second-moment twirl operator `M²(O⊗O)`; a separate
zero-mean first-moment result is what lets downstream users read this second moment as a centered
loss variance. The operator lies in `(g⊗g)^g = gTensorGInvariant b` (`mem_invariant`), which by
Schur's lemma is the one-dimensional line `span{C}` (`invariant_eq_spanC`). -/
structure RagoneSecondMoment {gens : Set (Matrix (Fin N) (Fin N) ℂ)} (b : DLAHermBasis gens)
    (ρ O : Matrix (Fin N) (Fin N) ℂ) where
  /-- The loss second moment; under a separately proved zero-mean condition, the loss variance
  (the generic zero-mean input is `repTwirl_trace_pairing_eq_zero_of_trace_eq_zero` and the
  centering identity is `secondMoment_eq_centered_of_mean_zero`, both in `QuantumAlg/Util/Haar`). -/
  variance : ℝ
  /-- The second-moment (twirl) operator evaluated at `O ⊗ O`. -/
  secondMoment : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ
  /-- Step 2 (Haar second moment): `M₂ = ⟪ρ⊗ρ, M²(O⊗O)⟫`. The `variance` field records this loss
  second moment; the zero-mean first-moment lemma identifying it with the centered loss variance
  is `repTwirl_trace_pairing_eq_zero_of_trace_eq_zero` + `secondMoment_eq_centered_of_mean_zero`
  (`QuantumAlg/Util/Haar`), applied per concrete ensemble. -/
  var_eq : (variance : ℂ) = hsInner (ρ ⊗ₖ ρ) secondMoment
  /-- Steps 4–6 (H-INV): the second-moment operator `M²(O⊗O)` lies in the `g`-invariant subspace
  `(g⊗g)^g = gTensorGInvariant b`. This replaces the earlier false full-space membership in
  `span{C}`: the genuine twirl is `g`-invariant only after restricting to `g ⊗ g`. -/
  mem_invariant : secondMoment ∈ gTensorGInvariant b
  /-- Step 7 (H2 / Schur — a named hypothesis): the invariant subspace `(g⊗g)^g` is the line
  `span{C}` spanned by the quadratic Casimir. Discharged by proof for the trivial DLA
  (`trivialDLA_invariant_eq_spanC`); a genuine Schur proof for general `g` is deferred. -/
  invariant_eq_spanC : gTensorGInvariant b = Submodule.span ℂ {b.casimir}
  /-- Step 4 (orthogonal projection): residual `⊥ C`, i.e. `⟪C,O⊗O⟫ = ⟪C,M²(O⊗O)⟫`. -/
  proj_orth : hsInner b.casimir (O ⊗ₖ O) = hsInner b.casimir secondMoment

/-- **Derived membership in `span{C}`** (formerly the posited `proj_mem` field). The second moment
is a scalar multiple of the Casimir — now a *consequence* of `mem_invariant` (it
lands in `(g⊗g)^g`) and `invariant_eq_spanC` (`(g⊗g)^g = span{C}`), no longer a free assumption. -/
theorem RagoneSecondMoment.proj_mem {gens : Set (Matrix (Fin N) (Fin N) ℂ)}
    {b : DLAHermBasis gens} {ρ O : Matrix (Fin N) (Fin N) ℂ} (M : RagoneSecondMoment b ρ O) :
    ∃ κ : ℂ, M.secondMoment = κ • b.casimir := by
  have h := M.mem_invariant
  rw [M.invariant_eq_spanC, Submodule.mem_span_singleton] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha.symm⟩

/-- **The Lie-algebraic loss second-moment formula (simple-DLA case)** —
[RBS+23, Arxiv_Final.tex:691], the `k=1` case. Given the bundled Haar/twirl/Schur
hypotheses and Hermitian `ρ`, `O`, the loss second moment is `P_g(ρ) · P_g(O) / dim(g)`.
With a separately proved zero-mean condition, this is the loss variance.
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

/-- **Consistency witness — NOT the physical Haar twirl.** For any Hermitian basis `b` and
Hermitian `ρ`, `O`, given the Schur hypothesis `hSchur` (which IS proved for the trivial DLA,
`trivialDLA_invariant_eq_spanC`), the reshaped `RagoneSecondMoment` bundle is satisfiable —
witnessed by hand-setting `secondMoment := (P_g(O)/dim) • C`. This exhibits internal consistency
(so `variance_eq_gPurity` is **not vacuously true**) and is now NON-CIRCULAR: `mem_invariant` is
discharged by `casimir_mem_gTensorGInvariant` (the Casimir genuinely lies in `(g⊗g)^g`), not
posited. It does **not** construct the genuine `2`-design twirl — that derivation is deferred. -/
noncomputable def RagoneSecondMoment.consistencyWitness {gens : Set (Matrix (Fin N) (Fin N) ℂ)}
    {b : DLAHermBasis gens} {ρ O : Matrix (Fin N) (Fin N) ℂ}
    (hρ : ρᴴ = ρ) (hO : Oᴴ = O) (hdim : 0 < b.dim)
    (hSchur : gTensorGInvariant b = Submodule.span ℂ {b.casimir}) :
    RagoneSecondMoment b ρ O where
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
  mem_invariant := Submodule.smul_mem _ _ (casimir_mem_gTensorGInvariant b)
  invariant_eq_spanC := hSchur
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
assumption): the assumed (Haar/Schur) inputs are the per-ideal diagonal memberships of the
second-moment blocks, the SEPARATELY named cross-ideal invariant-block exclusion, and the
per-ideal Schur lines `span{Cⱼ}`. -/

/-- **Reductive-case input** [RBS+23, Arxiv_Final.tex:674, 682] (Theorem 1 / Eq. (9)). The
orthogonal direct-sum decomposition `g = ⊕ⱼ gⱼ` together with the per-ideal second-moment
blocks; the exclusion of cross-ideal invariant blocks is carried by its own named hypothesis
field (`cross_block_exclusion`), parallel to the twirl (H1) and Schur (H2) inputs. -/
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
  /-- Total loss second moment; under a separately proved zero-mean condition, the loss variance
  (the generic zero-mean input is `repTwirl_trace_pairing_eq_zero_of_trace_eq_zero` and the
  centering identity is `secondMoment_eq_centered_of_mean_zero`, both in `QuantumAlg/Util/Haar`). -/
  variance : ℝ
  /-- The second-moment (twirl) operator at `O ⊗ O`. -/
  secondMoment : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ
  /-- The per-ideal diagonal blocks of the second moment: `diagBlock j` is the
  component attributed to the ideal block `gⱼ ⊗ gⱼ`. -/
  diagBlock : Fin numComp → Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ
  /-- Step 2 (Haar second moment): `M₂ = ⟪ρ⊗ρ, M²(O⊗O)⟫`. The `variance` field records this loss
  second moment; the zero-mean first-moment lemma identifying it with the centered loss variance
  is `repTwirl_trace_pairing_eq_zero_of_trace_eq_zero` + `secondMoment_eq_centered_of_mean_zero`
  (`QuantumAlg/Util/Haar`), applied per concrete ensemble. -/
  var_eq : (variance : ℂ) = hsInner (ρ ⊗ₖ ρ) secondMoment
  /-- Steps 4–6 (H-INV, per ideal): each diagonal block lies in its own ideal's invariant
  space `(gⱼ⊗gⱼ)^gⱼ = gTensorGInvariant (basis j)`. -/
  diagBlock_mem_invariant : ∀ j, diagBlock j ∈ gTensorGInvariant (basis j)
  /-- **Cross-ideal invariant-block exclusion (H-CROSS / Schur across ideals — a named
  hypothesis)**: the second moment is exhausted by its per-ideal diagonal blocks. This is a
  non-trivial input, not a free consequence of finite twirling. The finite-group doubled commutant
  can be larger than the Lie-algebra invariant space `(g⊗g)^g`; after restricting to `(g⊗g)^g`,
  cross blocks still need their own exclusion argument. For commuting centre-free ideals, those
  cross blocks vanish inside `(g⊗g)^g`; the public declaration `so4_gTensorGInvariant_finrank`
  records the SO(4) decomposition pattern. This field records the resulting diagonal-block
  exhaustion, parallel to the twirl (H1) and per-ideal Schur (H2) inputs. The record deliberately
  carries no `cross_commute` field — the components are only required to be cross-orthogonal, not
  commuting ideals — so the exhaustion cannot be derived from the record's own hypotheses; adding
  such a field is a named-hypothesis structure change reserved for an explicit owner decision. -/
  cross_block_exclusion : secondMoment = ∑ j, diagBlock j
  /-- Step 7 (H2 / Schur, per ideal): each ideal's invariant subspace `(gⱼ⊗gⱼ)^gⱼ` is the line
  `span{Cⱼ}`. A named hypothesis (proved for the trivial DLA; the general Schur proof is deferred).
-/
  invariant_eq_spanC : ∀ j, gTensorGInvariant (basis j) = Submodule.span ℂ {(basis j).casimir}
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

/-- **Derived diagonal-sum membership** (formerly the posited `mem_invariant` field). The
second moment lies in the per-ideal diagonal invariant space `⨆ⱼ (gⱼ⊗gⱼ)^gⱼ` — now a
*consequence* of the per-ideal diagonal memberships (`diagBlock_mem_invariant`) and the named
cross-ideal invariant-block exclusion (`cross_block_exclusion`), no longer a single fused
assumption. -/
theorem mem_invariant : R.secondMoment ∈ ⨆ j, gTensorGInvariant (R.basis j) := by
  rw [R.cross_block_exclusion]
  exact Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j (R.diagBlock_mem_invariant j)

/-- **Derived per-ideal projection** (formerly the posited `proj_mem` field). The second moment is
a linear combination of the per-ideal Casimirs — now a *consequence* of `mem_invariant`
(it lands in `⨆ⱼ (gⱼ⊗gⱼ)^gⱼ`, itself derived from the split fields) and `invariant_eq_spanC`
(each ideal's invariant space is `span{Cⱼ}`), no longer a free assumption. -/
theorem proj_mem :
    ∃ κ : Fin R.numComp → ℂ, R.secondMoment = ∑ j, κ j • (R.basis j).casimir := by
  have hle : (⨆ j, gTensorGInvariant (R.basis j))
      ≤ Submodule.span ℂ (Set.range fun j => (R.basis j).casimir) := by
    refine iSup_le fun j => ?_
    rw [R.invariant_eq_spanC j]
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨j, rfl⟩)
  obtain ⟨κ, hκ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hle R.mem_invariant)
  exact ⟨κ, hκ.symm⟩

/-- **Reductive-case second-moment formula — [RBS+23, Arxiv_Final.tex:682] (Eq. (9)), DERIVED.**
The total loss second moment is the sum over the ideals of `g = ⊕ⱼ gⱼ` of
`P_{gⱼ}(ρ)·P_{gⱼ}(O)/dim(gⱼ)`; under a separately proved zero-mean condition, it is the loss
variance. The
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

/-! ### Generic reductive consistency witness -/

/-- Cross-ideal Casimir orthogonality for a basis family with mutually orthogonal ideals. -/
theorem casimir_cross_aux {N : ℕ} {numComp : ℕ}
    {gens : Fin numComp → Set (Matrix (Fin N) (Fin N) ℂ)}
    (basis : (j : Fin numComp) → DLAHermBasis (gens j))
    (cross_ortho : ∀ i j, i ≠ j → ∀ a b, hsInner ((basis i).B a) ((basis j).B b) = 0)
    (i j : Fin numComp) :
    hsInner (basis i).casimir (basis j).casimir =
      if i = j then ((basis i).dim : ℂ) else 0 := by
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    exact (basis i).casimir_hsInner_self
  · rw [if_neg h, DLAHermBasis.casimir, DLAHermBasis.casimir, hsInner_sum_left]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hsInner_sum_right]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [hsInner_kronecker, cross_ortho i j h a b, zero_mul]

/-- **Reductive consistency witness from per-ideal Hermitian bases — NOT the physical twirl.** Given
the per-ideal Schur hypotheses `hSchur`, the reshaped `RagoneReductive` bundle is satisfiable,
witnessed by the per-ideal diagonal second moment `∑ⱼ (P_{gⱼ}(O)/dimⱼ)·Cⱼ`. It is NON-CIRCULAR:
the per-ideal diagonal memberships (`diagBlock_mem_invariant`) are discharged from
`casimir_mem_gTensorGInvariant`, not posited, and the cross-ideal invariant-block exclusion
(`cross_block_exclusion`) holds definitionally — the hand-set second moment is purely diagonal.
For the genuine twirl the exclusion is the deferred Schur-across-ideals input. -/
noncomputable def RagoneReductive.consistencyWitness {N : ℕ}
    {ρ O : Matrix (Fin N) (Fin N) ℂ}
    (numComp : ℕ) (gens : Fin numComp → Set (Matrix (Fin N) (Fin N) ℂ))
    (basis : (j : Fin numComp) → DLAHermBasis (gens j))
    (cross_ortho : ∀ i j, i ≠ j → ∀ a b, hsInner ((basis i).B a) ((basis j).B b) = 0)
    (hρ : ρᴴ = ρ) (hO : Oᴴ = O) (hdim : ∀ j, 0 < (basis j).dim)
    (hSchur : ∀ j, gTensorGInvariant (basis j) = Submodule.span ℂ {(basis j).casimir}) :
    RagoneReductive ρ O where
  numComp := numComp
  gens := gens
  basis := basis
  cross_ortho := cross_ortho
  variance := (∑ j, (basis j).gPurity ρ * (basis j).gPurity O / ((basis j).dim : ℂ)).re
  secondMoment := ∑ j, ((basis j).gPurity O / ((basis j).dim : ℂ)) • (basis j).casimir
  diagBlock := fun j => ((basis j).gPurity O / ((basis j).dim : ℂ)) • (basis j).casimir
  var_eq := by
    have hρρ : (ρ ⊗ₖ ρ)ᴴ = ρ ⊗ₖ ρ := by rw [conjTranspose_kronecker, hρ]
    have hterm : ∀ j, hsInner (ρ ⊗ₖ ρ)
          (((basis j).gPurity O / ((basis j).dim : ℂ)) • (basis j).casimir)
        = (basis j).gPurity ρ * (basis j).gPurity O / ((basis j).dim : ℂ) := by
      intro j
      rw [hsInner_smul_right, hsInner_comm_of_isHermitian hρρ (basis j).casimir_isHermitian,
        (basis j).casimir_hsInner_kron hρ]
      ring_nf
    have hSreal : (starRingEnd ℂ)
          (∑ j, (basis j).gPurity ρ * (basis j).gPurity O / ((basis j).dim : ℂ))
        = ∑ j, (basis j).gPurity ρ * (basis j).gPurity O / ((basis j).dim : ℂ) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_div₀, map_mul, (basis j).gPurity_conj ρ, (basis j).gPurity_conj O, map_natCast]
    rw [hsInner_sum_right, Finset.sum_congr rfl (fun j _ => hterm j)]
    exact Complex.conj_eq_iff_re.mp hSreal
  diagBlock_mem_invariant := fun j =>
    Submodule.smul_mem _ _ (casimir_mem_gTensorGInvariant (basis j))
  cross_block_exclusion := rfl
  invariant_eq_spanC := hSchur
  proj_orth := by
    intro j
    rw [(basis j).casimir_hsInner_kron hO, hsInner_sum_right]
    have hterm : ∀ i, hsInner (basis j).casimir
          (((basis i).gPurity O / ((basis i).dim : ℂ)) • (basis i).casimir)
        = if j = i then (basis j).gPurity O else 0 := by
      intro i
      rw [hsInner_smul_right, casimir_cross_aux basis cross_ortho j i]
      by_cases hji : j = i
      · subst hji
        rw [if_pos rfl, if_pos rfl, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (hdim j).ne')]
      · rw [if_neg hji, if_neg hji, mul_zero]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq]
    simp

/-! ### Capstone: exponentially large DLA ⟹ barren plateau (second-moment form) -/

/-- **Capstone — the full chain circuit ⟹ DLA ⟹ dimension ⟹ second moment ⟹ barren
plateau.** For a qubit-indexed family of simple-DLA circuits whose loss second moment is the
genuine value `P_g(ρ)·P_g(O)/dim(g)` [RBS+23, Arxiv_Final.tex:691] (the `RagoneSecondMoment`
bundle; read as loss variance after a separate zero-mean first-moment result), if the
`g`-purity numerator stays bounded and the dynamical Lie algebra dimension grows
exponentially in the qubit count, then the loss has a barren plateau. This consumes the
*proved* second-moment formula (`variance_eq_gPurity`) rather than an assumed variance law. -/
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

/-- BP scaling with an observable Hilbert-Schmidt numerator. If `‖P_g(ρ)‖ ≤ 1`,
`‖P_g(O)‖ ≤ 2^n`, and `dim g` grows at least like `base^n` for `base > 2`, then the
loss second moment is exponentially concentrated with rate `base / 2`; this is loss variance
after a separate zero-mean first-moment result. -/
theorem ragone_hasBarrenPlateau_normObs {sz : ℕ → ℕ}
    {gens : (n : ℕ) → Set (Matrix (Fin (sz n)) (Fin (sz n)) ℂ)}
    {ρ O : (n : ℕ) → Matrix (Fin (sz n)) (Fin (sz n)) ℂ}
    {b : (n : ℕ) → DLAHermBasis (gens n)}
    (M : (n : ℕ) → RagoneSecondMoment (b n) (ρ n) (O n))
    (hρ : ∀ n, (ρ n)ᴴ = ρ n) (hO : ∀ n, (O n)ᴴ = O n) (hdimpos : ∀ n, 0 < (b n).dim)
    (hρpurity : ∀ n, ‖(b n).gPurity (ρ n)‖ ≤ 1)
    (hOpurity : ∀ n, ‖(b n).gPurity (O n)‖ ≤ (2 : ℝ) ^ n)
    {base : ℝ} (hbase : 2 < base) (hexp : ∀ n, base ^ n ≤ ((b n).dim : ℝ)) :
    HasBarrenPlateau (fun n => (M n).variance) := by
  refine ⟨base / 2, by linarith, 1, zero_le_one, fun n => ?_⟩
  have hnum : ‖(b n).gPurity (ρ n) * (b n).gPurity (O n)‖ ≤ (2 : ℝ) ^ n := by
    rw [norm_mul]
    calc ‖(b n).gPurity (ρ n)‖ * ‖(b n).gPurity (O n)‖
        ≤ 1 * (2 : ℝ) ^ n :=
          mul_le_mul (hρpurity n) (hOpurity n) (norm_nonneg _) zero_le_one
      _ = (2 : ℝ) ^ n := one_mul _
  have hv : ((M n).variance : ℂ)
      = (b n).gPurity (ρ n) * (b n).gPurity (O n) / ((b n).dim : ℂ) :=
    (M n).variance_eq_gPurity (hρ n) (hO n) (hdimpos n)
  have hcast : |(M n).variance| = ‖((M n).variance : ℂ)‖ := (RCLike.norm_ofReal (K := ℂ) _).symm
  rw [sub_zero, hcast, hv, norm_div, RCLike.norm_natCast]
  refine (div_le_div₀ (by positivity) hnum (pow_pos (by linarith) n) (hexp n)).trans
    (le_of_eq ?_)
  rw [div_pow, one_div_div]

/-- BP scaling in Hilbert-Schmidt-norm form. A normalized state bound
`Tr[ρᴴρ] ≤ 1`, an observable bound `Tr[OᴴO] ≤ 2^n`, and `dim g ≥ base^n` with
`base > 2` imply a barren plateau. The purity bounds are discharged by the
Bessel inequality `DLAHermBasis.gPurity_le_normSq`. -/
theorem ragone_hasBarrenPlateau_hsNorm {sz : ℕ → ℕ}
    {gens : (n : ℕ) → Set (Matrix (Fin (sz n)) (Fin (sz n)) ℂ)}
    {ρ O : (n : ℕ) → Matrix (Fin (sz n)) (Fin (sz n)) ℂ}
    {b : (n : ℕ) → DLAHermBasis (gens n)}
    (M : (n : ℕ) → RagoneSecondMoment (b n) (ρ n) (O n))
    (hρ : ∀ n, (ρ n)ᴴ = ρ n) (hO : ∀ n, (O n)ᴴ = O n) (hdimpos : ∀ n, 0 < (b n).dim)
    (hρnorm : ∀ n, (hsInner (ρ n) (ρ n)).re ≤ 1)
    (hOnorm : ∀ n, (hsInner (O n) (O n)).re ≤ (2 : ℝ) ^ n)
    {base : ℝ} (hbase : 2 < base) (hexp : ∀ n, base ^ n ≤ ((b n).dim : ℝ)) :
    HasBarrenPlateau (fun n => (M n).variance) := by
  refine ragone_hasBarrenPlateau_normObs M hρ hO hdimpos (fun n => ?_) (fun n => ?_) hbase hexp
  · rw [(b n).norm_gPurity_eq_re]
    exact ((b n).gPurity_le_normSq (ρ n)).trans (hρnorm n)
  · rw [(b n).norm_gPurity_eq_re]
    exact ((b n).gPurity_le_normSq (O n)).trans (hOnorm n)

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

/-- **The Schur hypothesis (H2) is PROVABLE for the trivial DLA.** On the one-dimensional doubled
operator space `Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ`, the invariant subspace `(g⊗g)^g` equals
`span{C}` — not as a posited hypothesis but by proof. This is the honest non-vacuity anchor: it lets
`consistencyWitness` build a satisfiable bundle whose `invariant_eq_spanC` field is genuinely
discharged, so the reshaped variance law is non-vacuous without re-introducing any circularity. -/
theorem trivialDLA_invariant_eq_spanC :
    gTensorGInvariant trivialDLAHermBasis
      = Submodule.span ℂ {trivialDLAHermBasis.casimir} := by
  have hC : ∀ p q : Fin 1 × Fin 1, trivialDLAHermBasis.casimir p q = 1 := by
    intro p q
    simp only [DLAHermBasis.casimir, trivialDLAHermBasis, Finset.univ_unique,
      Finset.sum_singleton, Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Subsingleton.elim p.1 q.1, Subsingleton.elim p.2 q.2, if_true, mul_one]
  have hTop : (⊤ : Submodule ℂ (Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ))
      = Submodule.span ℂ {trivialDLAHermBasis.casimir} := by
    refine le_antisymm (fun X _ => ?_) le_top
    rw [Submodule.mem_span_singleton]
    refine ⟨X default default, ?_⟩
    ext i j
    rw [Matrix.smul_apply, hC, smul_eq_mul, mul_one, Subsingleton.elim i default,
      Subsingleton.elim j default]
  exact le_antisymm (le_top.trans hTop.le)
    (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (casimir_mem_gTensorGInvariant _)))

/-- **The full hypothesis stack is non-vacuous.** There is a concrete dynamical Lie
algebra with a Hermitian orthonormal basis and a satisfiable second-moment bundle —
so the variance formula `variance_eq_gPurity` and the barren-plateau capstone are not
vacuously true. -/
theorem ragone_hypotheses_nonempty :
    ∃ (gens : Set (Matrix (Fin 1) (Fin 1) ℂ)) (b : DLAHermBasis gens)
      (ρ O : Matrix (Fin 1) (Fin 1) ℂ), Nonempty (RagoneSecondMoment b ρ O) :=
  ⟨_, trivialDLAHermBasis, 1, 1,
    ⟨RagoneSecondMoment.consistencyWitness conjTranspose_one conjTranspose_one Nat.one_pos
      trivialDLA_invariant_eq_spanC⟩⟩

/-- **The reductive hypothesis stack is non-vacuous.** A one-ideal instance of
`RagoneReductive` (built from the trivial DLA and its satisfiable second-moment bundle), so the
*derived* Eq. (9) sum `RagoneReductive.totalVariance_eq` is not vacuously true. -/
theorem ragone_reductive_nonempty :
    Nonempty (RagoneReductive (1 : Matrix (Fin 1) (Fin 1) ℂ) (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  let M := RagoneSecondMoment.consistencyWitness (b := trivialDLAHermBasis)
    conjTranspose_one conjTranspose_one Nat.one_pos trivialDLA_invariant_eq_spanC
  exact ⟨{
    numComp := 1
    gens := fun _ => {1}
    basis := fun _ => trivialDLAHermBasis
    cross_ortho := fun i j hij => absurd (Subsingleton.elim i j) hij
    variance := M.variance
    secondMoment := M.secondMoment
    diagBlock := fun _ => M.secondMoment
    var_eq := M.var_eq
    diagBlock_mem_invariant := fun _ => M.mem_invariant
    cross_block_exclusion := (Fin.sum_univ_one fun _ => M.secondMoment).symm
    invariant_eq_spanC := fun _ => trivialDLA_invariant_eq_spanC
    proj_orth := fun _ => M.proj_orth }⟩

end QuantumAlg
