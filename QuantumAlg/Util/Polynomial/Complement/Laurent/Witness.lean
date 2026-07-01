/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.Polynomial.Complement.Laurent.Certificate
public import QuantumAlg.Init
public import QuantumAlg.Util.Complex
public import QuantumAlg.Util.Polynomial.Laurent
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Trigonometric polynomial factorization helpers

Quantum-free Laurent/Fourier helpers for source theorems that construct a
complementary trigonometric polynomial.  The source-facing Fejer-Riesz style
existence proof is developed separately; this file records the small algebraic
interface that connects such a factorization to the QSP normalization equation.
-/

@[expose] public section

namespace QuantumAlg

open Polynomial Complex

noncomputable section

namespace Complement.Laurent

/-- The inverse-conjugate root pairing `z ↦ 1 / z*` used in Wang's Laurent
complement proof [WZYW23, arxiv_v3.tex:2241-2248]. -/
def reciprocalConj (z : ℂ) : ℂ :=
  (starRingEnd ℂ z)⁻¹

/-- The inverse-conjugate map preserves nonzero roots. -/
theorem reciprocalConj_ne_zero {z : ℂ} (hz : z ≠ 0) :
    reciprocalConj z ≠ 0 := by
  exact inv_ne_zero (by simpa [star_ne_zero] using hz)

/-- The inverse-conjugate map is an involution. -/
theorem reciprocalConj_involutive (z : ℂ) :
    reciprocalConj (reciprocalConj z) = z := by
  simp [reciprocalConj]

/-- The inverse-conjugate map is injective. -/
theorem reciprocalConj_injective : Function.Injective reciprocalConj := by
  intro z w h
  rw [← reciprocalConj_involutive z, h, reciprocalConj_involutive w]

/-- The inverse-conjugate map inverts the squared norm. -/
theorem normSq_reciprocalConj (z : ℂ) :
    Complex.normSq (reciprocalConj z) = (Complex.normSq z)⁻¹ := by
  simp [reciprocalConj, Complex.normSq_conj]

/-- Inverse-conjugation sends roots outside the unit circle inside it. -/
theorem normSq_reciprocalConj_lt_one_of_one_lt_normSq {z : ℂ}
    (h : 1 < Complex.normSq z) :
    Complex.normSq (reciprocalConj z) < 1 := by
  rw [normSq_reciprocalConj]
  exact inv_lt_one_of_one_lt₀ h

/-- Inverse-conjugation sends nonzero roots inside the unit circle outside it. -/
theorem one_lt_normSq_reciprocalConj_of_normSq_lt_one {z : ℂ}
    (hz : z ≠ 0) (h : Complex.normSq z < 1) :
    1 < Complex.normSq (reciprocalConj z) := by
  rw [normSq_reciprocalConj]
  exact (one_lt_inv₀ (Complex.normSq_pos.mpr hz)).mpr h

/-- Nonzero points fixed by inverse-conjugation lie on the unit circle. -/
theorem normSq_eq_one_of_reciprocalConj_eq_self {z : ℂ} (hz : z ≠ 0)
    (h : reciprocalConj z = z) :
    Complex.normSq z = 1 := by
  have hnorm := congrArg Complex.normSq h
  rw [normSq_reciprocalConj] at hnorm
  have hpos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  have hnonzero : Complex.normSq z ≠ 0 := hpos.ne'
  have hsquare : Complex.normSq z * Complex.normSq z = 1 := by
    calc
      Complex.normSq z * Complex.normSq z =
          (Complex.normSq z)⁻¹ * Complex.normSq z := by rw [hnorm]
      _ = 1 := inv_mul_cancel₀ hnonzero
  nlinarith [Complex.normSq_nonneg z]

/-- Nonzero unit-circle points are fixed by inverse-conjugation. -/
theorem reciprocalConj_eq_self_of_normSq_eq_one {z : ℂ}
    (h : Complex.normSq z = 1) :
    reciprocalConj z = z := by
  have hmul : starRingEnd ℂ z * z = 1 := by
    have hc : ((Complex.normSq z : ℝ) : ℂ) = 1 := by
      exact_mod_cast h
    rw [Complex.normSq_eq_conj_mul_self] at hc
    exact hc
  change (starRingEnd ℂ z)⁻¹ = z
  exact inv_eq_of_mul_eq_one_right hmul

/-- Off-unit-circle nonzero roots form distinct inverse-conjugate pairs. -/
theorem reciprocalConj_ne_self_of_normSq_ne_one {z : ℂ} (hz : z ≠ 0)
    (hunit : Complex.normSq z ≠ 1) :
    reciprocalConj z ≠ z := by
  intro h
  exact hunit (normSq_eq_one_of_reciprocalConj_eq_self hz h)

/-- Linear-factor form of Wang's identity
`e^{ix/2} - ξ = -e^{ix/2}ξ(e^{-ix/2} - 1/ξ)`, written as a reflected
polynomial identity [WZYW23, arxiv_v3.tex:2249-2251]. -/
theorem reflect_X_sub_C_conj (z : ℂ) (hz : z ≠ 0) :
    ((X : ℂ[X]) - C (starRingEnd ℂ z)).reflect 1 =
      C (-(starRingEnd ℂ z)) * (X - C (reciprocalConj z)) := by
  rw [Polynomial.reflect_sub, Polynomial.reflect_one_X, Polynomial.reflect_C]
  have hconj : starRingEnd ℂ z ≠ 0 := by
    simpa [star_ne_zero] using hz
  simp only [reciprocalConj, pow_one, map_neg, neg_mul]
  have hC :
      C ((starRingEnd ℂ) z) * C ((starRingEnd ℂ) z)⁻¹ = (1 : ℂ[X]) := by
    rw [← map_mul, mul_inv_cancel₀ hconj, map_one]
  rw [mul_sub, neg_sub]
  rw [hC]

/-- Reflected coefficient conjugation sends a power of a root factor at `z` to
the corresponding power of the inverse-conjugate root factor.  This is the
multiplicity-level version of Wang's linear identity
`e^{ix/2}-ξ = -e^{ix/2}ξ(e^{-ix/2}-1/ξ*)`
[WZYW23, arxiv_v3.tex:2249-2251]. -/
theorem reflect_conjP_X_sub_C_pow (z : ℂ) (m : ℕ) (hz0 : z ≠ 0) :
    (conjP (((X : ℂ[X]) - C z) ^ m)).reflect m =
      C ((-(starRingEnd ℂ z)) ^ m) * ((X : ℂ[X]) - C (reciprocalConj z)) ^ m := by
  rw [conjP_pow]
  have hbase := reflect_X_sub_C_conj z hz0
  induction m with
  | zero =>
      simp [Polynomial.reflect_one]
  | succ m ih =>
      rw [pow_succ]
      rw [Polynomial.reflect_mul _ _
        (by
          have hm :
              (conjP ((X : ℂ[X]) - C z) ^ m).natDegree ≤ m := by
            calc
              (conjP ((X : ℂ[X]) - C z) ^ m).natDegree =
                  m * (conjP ((X : ℂ[X]) - C z)).natDegree := by
                    rw [Polynomial.natDegree_pow]
              _ ≤ m := by
                    rw [conjP_sub, conjP_X, conjP_C]
                    have hle := Nat.mul_le_mul_left m
                      (Polynomial.natDegree_X_sub_C_le (R := ℂ)
                        (r := starRingEnd ℂ z))
                    omega
          exact hm)
        (by
          rw [conjP_sub, conjP_X, conjP_C]
          exact Polynomial.natDegree_X_sub_C_le (R := ℂ) (r := starRingEnd ℂ z))]
      rw [ih]
      rw [show conjP ((X : ℂ[X]) - C z) = (X : ℂ[X]) - C (starRingEnd ℂ z) by
        rw [conjP_sub, conjP_X, conjP_C]]
      rw [hbase]
      simp [pow_succ, mul_assoc, mul_comm, mul_left_comm]

/-- Coefficient conjugation on a product of linear root factors conjugates the
listed roots. -/
theorem conjP_multiset_prod_X_sub_C (roots : Multiset ℂ) :
    conjP ((roots.map fun z => (X : ℂ[X]) - C z).prod) =
      (roots.map fun z => (X : ℂ[X]) - C (starRingEnd ℂ z)).prod := by
  induction roots using Multiset.induction_on with
  | empty =>
      simp
  | cons z roots ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, conjP_mul, ih]
      rw [conjP_sub, conjP_X, conjP_C]
      rw [Multiset.map_cons, Multiset.prod_cons]

/-- Multiplying Wang's linear reflected-root identity over a selected root
multiset.  This is the product form of the step from
`e^{ix/2}-ξ` to `e^{-ix/2}-1/ξ` in the Laurent-complement proof
[WZYW23, arxiv_v3.tex:2249-2251]. -/
theorem reflect_conjP_multiset_prod_X_sub_C (roots : Multiset ℂ)
    (hroots0 : ∀ z ∈ roots, z ≠ 0) :
    (conjP ((roots.map fun z => (X : ℂ[X]) - C z).prod)).reflect roots.card =
      C ((roots.map fun z => -(starRingEnd ℂ z)).prod) *
        (roots.map fun z => (X : ℂ[X]) - C (reciprocalConj z)).prod := by
  induction roots using Multiset.induction_on with
  | empty =>
      simp
  | cons z roots ih =>
      have hz0 : z ≠ 0 := hroots0 z (by simp)
      have htail : ∀ w ∈ roots, w ≠ 0 := by
        intro w hw
        exact hroots0 w (by simp [hw])
      have hdeg_tail :
          ((roots.map fun w => (X : ℂ[X]) - C (starRingEnd ℂ w)).prod).natDegree ≤
            roots.card := by
        simpa using
          (Polynomial.natDegree_multiset_prod_X_sub_C_eq_card
            (roots.map fun w => starRingEnd ℂ w)).le
      rw [Multiset.map_cons, Multiset.prod_cons, conjP_mul,
        conjP_multiset_prod_X_sub_C]
      rw [conjP_sub, conjP_X, conjP_C]
      simp only [Multiset.card_cons]
      rw [show roots.card + 1 = 1 + roots.card by omega]
      rw [Polynomial.reflect_mul _ _ (Polynomial.natDegree_X_sub_C_le _) hdeg_tail]
      rw [reflect_X_sub_C_conj z hz0]
      rw [← conjP_multiset_prod_X_sub_C roots]
      rw [ih htail]
      simp [Multiset.map_cons, Multiset.prod_cons]
      ring

/-- Coefficient conjugation commutes with reflection. -/
theorem conjP_reflect (F : ℂ[X]) (L : ℕ) :
    conjP (F.reflect L) = (conjP F).reflect L := by
  ext k
  simp [conjP_coeff, Polynomial.coeff_reflect]

/-- The reflected-conjugate product representing `|F(x)|^2` under the Laurent
encoding. -/
abbrev normPolynomial (L : ℕ) (F : ℂ[X]) : ℂ[X] :=
  F * (conjP F).reflect L

/-- The residual Laurent polynomial `1-|F|²` at budget `L`, encoded as
`X^L - F·F*`.  This is the polynomial called `1-PP*` in Wang's Laurent
complement proof [WZYW23, arxiv_v3.tex:2260-2274]. -/
abbrev residualPolynomial (L : ℕ) (F : ℂ[X]) : ℂ[X] :=
  X ^ L - normPolynomial L F

/-- A Laurent square-root factorization at budget `L`: `B` is a square root of
`R` in the reflected-conjugate sense used by trigonometric QSP. -/
structure SquareRootCertificate (L : ℕ) (R : ℂ[X]) where
  /-- Laurent square-root polynomial for the residual target. -/
  root : ℂ[X]
  degree_root : root.degree ≤ L
  factor_eq : normPolynomial L root = R

/-- Root-product polynomial used in Wang's constructive square-root proof. -/
def sourceRootProduct (scale : ℂ) (roots : Multiset ℂ) : ℂ[X] :=
  C scale * (roots.map fun z => X - C z).prod

/-- Wang's selected-root product with unit source scale is nonzero. -/
theorem sourceRootProduct_one_ne_zero (roots : Multiset ℂ) :
    sourceRootProduct 1 roots ≠ 0 := by
  classical
  rw [sourceRootProduct]
  refine mul_ne_zero (by norm_num) ?_
  exact Multiset.prod_ne_zero (by
    intro hzero
    rcases Multiset.mem_map.mp hzero with ⟨z, _hz, hfactor⟩
    exact Polynomial.X_sub_C_ne_zero z hfactor)

/-- Split the source root product into its zero-root padding and nonzero root
product.  This is the algebraic bookkeeping used when Wang's construction
chooses one root from each nonzero reciprocal-conjugate pair and leaves zero
roots as Laurent-budget padding [WZYW23, arxiv_v3.tex:2237-2257]. -/
theorem sourceRootProduct_zero_nonzero_filter (scale : ℂ) (roots : Multiset ℂ) :
    sourceRootProduct scale roots =
      X ^ roots.count 0 *
        sourceRootProduct scale (roots.filter fun z : ℂ => z ≠ 0) := by
  classical
  have hsplit :
      roots = roots.filter (fun z : ℂ => z = 0) +
        roots.filter (fun z : ℂ => z ≠ 0) := by
    ext z
    by_cases hz : z = 0
    · simp [hz]
    · simp [hz]
  have hzero :
      ((roots.filter (fun z : ℂ => z = 0)).map fun z => X - C z).prod =
        (X : ℂ[X]) ^ roots.count 0 := by
    rw [Multiset.filter_eq']
    simp
  have hmap :
      roots.map (fun z => X - C z) =
        ((roots.filter (fun z : ℂ => z = 0) +
          roots.filter (fun z : ℂ => z ≠ 0)).map fun z => X - C z) := by
    conv_lhs => rw [hsplit]
  calc
    sourceRootProduct scale roots =
        C scale * (roots.map fun z => X - C z).prod := rfl
    _ = C scale *
        (((roots.filter (fun z : ℂ => z = 0) +
            roots.filter (fun z : ℂ => z ≠ 0)).map fun z => X - C z).prod) := by
          rw [hmap]
    _ = C scale *
        (((roots.filter (fun z : ℂ => z = 0)).map fun z => X - C z).prod *
          ((roots.filter (fun z : ℂ => z ≠ 0)).map fun z => X - C z).prod) := by
          simp [Multiset.map_add, Multiset.prod_add]
    _ = C scale *
        ((X : ℂ[X]) ^ roots.count 0 *
          ((roots.filter (fun z : ℂ => z ≠ 0)).map fun z => X - C z).prod) := by
          rw [hzero]
    _ = X ^ roots.count 0 *
        (C scale *
          ((roots.filter (fun z : ℂ => z ≠ 0)).map fun z => X - C z).prod) := by
          ring
    _ = X ^ roots.count 0 *
        sourceRootProduct scale (roots.filter fun z : ℂ => z ≠ 0) := rfl

/-- Root-product factorization with the zero-root padding expressed as root
multiplicity. -/
theorem sourceRootProduct_roots_zero_nonzero_filter (R : ℂ[X]) :
    sourceRootProduct R.leadingCoeff R.roots =
      X ^ R.rootMultiplicity 0 *
        sourceRootProduct R.leadingCoeff (R.roots.filter fun z : ℂ => z ≠ 0) := by
  rw [sourceRootProduct_zero_nonzero_filter, Polynomial.count_roots]

/-- The nonzero-root submultiset contains exactly the degree minus the
zero-root multiplicity. -/
theorem roots_filter_ne_zero_card (R : ℂ[X]) :
    (R.roots.filter fun z : ℂ => z ≠ 0).card =
      R.natDegree - R.rootMultiplicity 0 := by
  classical
  have hsplit :
      R.roots = R.roots.filter (fun z : ℂ => z = 0) +
        R.roots.filter (fun z : ℂ => z ≠ 0) := by
    ext z
    by_cases hz : z = 0
    · simp [hz]
    · simp [hz]
  have hzero_card :
      (R.roots.filter (fun z : ℂ => z = 0)).card = R.rootMultiplicity 0 := by
    rw [Multiset.filter_eq']
    simp [Polynomial.count_roots]
  have hcard := congrArg Multiset.card hsplit
  have hroots_card : R.roots.card = R.natDegree :=
    IsAlgClosed.card_roots_eq_natDegree (p := R)
  have hsum :
      R.natDegree =
        R.rootMultiplicity 0 +
          (R.roots.filter fun z : ℂ => z ≠ 0).card := by
    simpa [hroots_card, hzero_card, Multiset.card_add] using hcard
  omega

/-- A selected root product has reflected-conjugate norm equal to the product
over the selected roots and their reciprocal-conjugates.  This is the algebraic
bridge from Wang's selected half of the roots to the Laurent square-root
certificate [WZYW23, arxiv_v3.tex:2249-2257]. -/
theorem normPolynomial_sourceRootProduct (scale : ℂ) (roots : Multiset ℂ)
    (hroots0 : ∀ z ∈ roots, z ≠ 0) :
    normPolynomial roots.card (sourceRootProduct scale roots) =
      sourceRootProduct
        (scale * starRingEnd ℂ scale *
          (roots.map fun z => -(starRingEnd ℂ z)).prod)
        (roots + roots.map reciprocalConj) := by
  rw [normPolynomial, sourceRootProduct, conjP_mul, conjP_C]
  rw [Polynomial.reflect_C_mul]
  rw [reflect_conjP_multiset_prod_X_sub_C roots hroots0]
  simp [sourceRootProduct, Multiset.map_add, Multiset.prod_add]
  ring

/-- A selected half of the reciprocal-conjugate root pairs for a target
polynomial.  Producing this data is the remaining root-classification content
of Wang's Laurent complement proof; the algebraic conversion to a square-root
certificate is `ReciprocalConjRootSelection.toSourceSquareRootCertificate`
[WZYW23, arxiv_v3.tex:2241-2257]. -/
structure ReciprocalConjRootSelection (L : ℕ) (R : ℂ[X]) where
  /-- Source scalar multiplying the selected root product. -/
  scale : ℂ
  /-- Selected half of the reciprocal-conjugate root pairs. -/
  roots : Multiset ℂ
  roots_card_eq : roots.card = L
  roots_nonzero : ∀ z ∈ roots, z ≠ 0
  pair_factor_eq :
    sourceRootProduct
        (scale * starRingEnd ℂ scale *
          (roots.map fun z => -(starRingEnd ℂ z)).prod)
        (roots + roots.map reciprocalConj) = R

/-- A selected nonzero part of the reciprocal-conjugate root pairs, allowing
the remaining budget to be supplied by zero-root padding.  This is the right
source-facing shape for Wang's Laurent-complement proof when the residual has
roots at the origin [WZYW23, arxiv_v3.tex:2237-2274]. -/
structure PaddedReciprocalConjRootSelection (L : ℕ) (R : ℂ[X]) where
  /-- Source scalar multiplying the selected nonzero root product. -/
  scale : ℂ
  /-- Selected nonzero roots before zero-root padding. -/
  roots : Multiset ℂ
  roots_card_le : roots.card ≤ L
  roots_nonzero : ∀ z ∈ roots, z ≠ 0
  padded_pair_factor_eq :
    X ^ (L - roots.card) *
      sourceRootProduct
        (scale * starRingEnd ℂ scale *
          (roots.map fun z => -(starRingEnd ℂ z)).prod)
        (roots + roots.map reciprocalConj) = R

/-- Wang's source-facing root-product square-root certificate: a selected half
of the reciprocal-conjugate root pairs, together with the source scalar,
constructs a Laurent polynomial whose reflected-conjugate norm is the target
residual [WZYW23, arxiv_v3.tex:2249-2257]. -/
structure SourceSquareRootCertificate (L : ℕ) (R : ℂ[X]) where
  /-- Source scalar multiplying the selected root product. -/
  scale : ℂ
  /-- Selected roots used to form the square-root polynomial. -/
  roots : Multiset ℂ
  roots_card_le : roots.card ≤ L
  factor_eq : normPolynomial L (sourceRootProduct scale roots) = R

/-- A reciprocal-conjugate root selection yields Wang's root-product
square-root certificate. -/
def ReciprocalConjRootSelection.toSourceSquareRootCertificate {L : ℕ} {R : ℂ[X]}
    (h : ReciprocalConjRootSelection L R) :
    SourceSquareRootCertificate L R where
  scale := h.scale
  roots := h.roots
  roots_card_le := le_of_eq h.roots_card_eq
  factor_eq := by
    have hnorm :=
      normPolynomial_sourceRootProduct h.scale h.roots h.roots_nonzero
    simpa [h.roots_card_eq] using hnorm.trans h.pair_factor_eq

/-- Source-facing factorization of a complex polynomial into all of its roots.
This records the first step of Wang's Laurent-complement proof before the roots
are classified into reciprocal-conjugate pairs [WZYW23, arxiv_v3.tex:2241-2248]. -/
structure FullRootProductFactorization (R : ℂ[X]) where
  /-- Leading scalar for the full root product. -/
  scale : ℂ
  /-- Full multiset of roots in the source product factorization. -/
  roots : Multiset ℂ
  factor_eq : sourceRootProduct scale roots = R

/-- A complementary Laurent polynomial for `A` at budget `L`. -/
structure ComplementCertificate (L : ℕ) (A : ℂ[X]) where
  /-- Complementary Laurent polynomial paired with `A`. -/
  complement : ℂ[X]
  degree_complement : complement.degree ≤ L
  normalization : normPolynomial L A + normPolynomial L complement = X ^ L

/-- The zero target is complemented by the constant Laurent polynomial `1`.
This is the simplest zero-root padding case in the Laurent-complement problem. -/
def ComplementCertificate.ofZeroTarget (L : ℕ) :
    ComplementCertificate L 0 where
  complement := 1
  degree_complement := by
    rw [Polynomial.degree_one]
    exact WithBot.coe_le_coe.mpr (Nat.zero_le L)
  normalization := by
    rw [normPolynomial, normPolynomial]
    simp [conjP_one, Polynomial.reflect_one]

/-- Pointwise boundedness of a Laurent/Fourier polynomial on the unit circle,
in the `lEval` encoding used by trigonometric QSP. -/
abbrev BoundedOnCircle (L : ℕ) (A : ℂ[X]) : Prop :=
  ∀ x : ℝ, ‖lEval L A x‖ ≤ 1

namespace Witness

/-- Staged Laurent-complement certificate type. -/
abbrev ComplementCertificate (L : ℕ) (A : ℂ[X]) :=
  Complement.Laurent.ComplementCertificate L A

/-- The source-facing complement existence problem from Wang's appendix:
a bounded Laurent polynomial admits a reflected-conjugate complement.  This is
the Lean target corresponding to the root-factor proof in
[WZYW23, arxiv_v3.tex:2233-2274]. -/
def HasComplement (L : ℕ) (A : ℂ[X]) : Prop :=
  Nonempty (Complement.Laurent.ComplementCertificate L A)

/-- The zero target has a Laurent complement. -/
theorem hasComplement_zero (L : ℕ) :
    HasComplement L (0 : ℂ[X]) :=
  ⟨Complement.Laurent.ComplementCertificate.ofZeroTarget L⟩

end Witness

/-- Compatibility name for the staged Laurent-complement existence predicate. -/
abbrev HasComplement (L : ℕ) (A : ℂ[X]) : Prop :=
  Witness.HasComplement L A

/-- Compatibility name for the staged zero-target Laurent complement witness. -/
theorem hasComplement_zero (L : ℕ) :
    HasComplement L (0 : ℂ[X]) :=
  Witness.hasComplement_zero L

/-- Data package for the bounded Laurent complement theorem before choosing a
particular complement. -/
abbrev BoundedComplementProblem :=
  Complement.Laurent.Problem.BoundedComplementProblem

/-! ### Local sign-change helpers -/

/-- Extract one point on each side of a real point from a neighborhood
eventuality. -/
theorem exists_left_right_of_eventually_nhds' {s : ℝ} {p : ℝ → Prop}
    (hp : ∀ᶠ x in nhds s, p x) :
    ∃ x y, x < s ∧ s < y ∧ p x ∧ p y := by
  rcases Metric.eventually_nhds_iff.mp hp with ⟨ε, hε, hball⟩
  let δ : ℝ := ε / 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    linarith
  have hδlt : δ < ε := by
    dsimp [δ]
    linarith
  refine ⟨s - δ, s + δ, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · apply hball
    rw [Real.dist_eq]
    have hsub : s - δ - s = -δ := by ring
    have hnegδ : -δ < 0 := by linarith
    rw [hsub, abs_of_neg hnegδ]
    simpa using hδlt
  · apply hball
    rw [Real.dist_eq]
    have hsub : s + δ - s = δ := by ring
    rw [hsub, abs_of_pos hδpos]
    exact hδlt

/-- A real function that is locally nonnegative cannot have an odd-order
isolated zero in a local factorization.  This is the real-analysis core of the
unit-circle root multiplicity step in Wang's Laurent-complement proof
[WZYW23, arxiv_v3.tex:2241-2257]. -/
theorem even_of_eventually_nonnegative_local_pow {s : ℝ} {m : ℕ}
    {f q : ℝ → ℝ}
    (hnonneg : ∀ᶠ t in nhds s, 0 ≤ f t)
    (hfactor : ∀ᶠ t in nhds s, f t = (t - s) ^ m * q t)
    (hq_cont : ContinuousAt q s) (hq_ne : q s ≠ 0) :
    Even m := by
  by_contra hnot
  have hodd : Odd m := Nat.not_even_iff_odd.mp hnot
  rcases lt_or_gt_of_ne hq_ne with hq_neg | hq_pos
  · have hq_eventually : ∀ᶠ t in nhds s, q t < 0 := by
      have hpre :
          (fun t : ℝ => q t) ⁻¹' Set.Iio 0 ∈ nhds s :=
        hq_cont.preimage_mem_nhds (Iio_mem_nhds hq_neg)
      simpa [Filter.Eventually, Set.preimage, Set.Iio] using hpre
    have hp :
        ∀ᶠ t in nhds s,
          0 ≤ f t ∧ f t = (t - s) ^ m * q t ∧ q t < 0 :=
      hnonneg.and (hfactor.and hq_eventually)
    rcases exists_left_right_of_eventually_nhds' hp with
      ⟨_x, y, _hxs, hsy, _hx, hy⟩
    have hysub : 0 < y - s := sub_pos.mpr hsy
    have hpow_pos : 0 < (y - s) ^ m := pow_pos hysub _
    have hf_neg : f y < 0 := by
      rw [hy.2.1]
      exact mul_neg_of_pos_of_neg hpow_pos hy.2.2
    linarith
  · have hq_eventually : ∀ᶠ t in nhds s, 0 < q t := by
      have hpre :
          (fun t : ℝ => q t) ⁻¹' Set.Ioi 0 ∈ nhds s :=
        hq_cont.preimage_mem_nhds (Ioi_mem_nhds hq_pos)
      simpa [Filter.Eventually, Set.preimage, Set.Ioi] using hpre
    have hp :
        ∀ᶠ t in nhds s,
          0 ≤ f t ∧ f t = (t - s) ^ m * q t ∧ 0 < q t :=
      hnonneg.and (hfactor.and hq_eventually)
    rcases exists_left_right_of_eventually_nhds' hp with
      ⟨x, _y, hxs, _hsy, hx, _hy⟩
    have hxsub : x - s < 0 := sub_neg.mpr hxs
    have hpow_neg : (x - s) ^ m < 0 :=
      (Odd.pow_neg_iff hodd).mpr hxsub
    have hf_neg : f x < 0 := by
      rw [hx.2.1]
      exact mul_neg_of_neg_of_pos hpow_neg hx.2.2
    linarith

/-- Complex-valued version of `even_of_eventually_nonnegative_local_pow`.
When a complex local factorization is real-valued near the root and its real
part is nonnegative, the order is even.  This matches the local shape of
Wang's unit-circle residual after parametrizing the circle
[WZYW23, arxiv_v3.tex:2241-2257]. -/
theorem even_of_eventually_nonnegative_local_complex_pow {s : ℝ} {m : ℕ}
    {f q : ℝ → ℂ}
    (hnonneg : ∀ᶠ t in nhds s, 0 ≤ (f t).re)
    (hfactor :
      ∀ᶠ t in nhds s, f t = (((t - s) ^ m : ℝ) : ℂ) * q t)
    (hq_cont : ContinuousAt q s)
    (hq_real : ∀ᶠ t in nhds s, (q t).im = 0)
    (hq_ne : q s ≠ 0) :
    Even m := by
  have hq_re_ne : (fun t : ℝ => (q t).re) s ≠ 0 := by
    intro hzero
    have him : (q s).im = 0 := hq_real.self_of_nhds
    exact hq_ne (Complex.ext hzero him)
  exact
    even_of_eventually_nonnegative_local_pow
      (s := s) (m := m) (f := fun t : ℝ => (f t).re)
      (q := fun t : ℝ => (q t).re)
      hnonneg
      (hfactor.mono fun t ht => by
        rw [ht, Complex.re_ofReal_mul])
      (Complex.continuous_re.continuousAt.comp hq_cont) hq_re_ne

/-- A version of `even_of_eventually_nonnegative_local_complex_pow` that derives
the needed real-valuedness of the local factor from the fact that the product
`f` is real-valued near the root.  This is the local analytic step behind the
unit-circle root multiplicity argument in Wang's Laurent-complement proof
[WZYW23, arxiv_v3.tex:2241-2257]. -/
theorem even_of_eventually_nonnegative_realvalued_local_complex_pow {s : ℝ} {m : ℕ}
    {f q : ℝ → ℂ}
    (hnonneg : ∀ᶠ t in nhds s, 0 ≤ (f t).re)
    (hf_real : ∀ᶠ t in nhds s, (f t).im = 0)
    (hfactor :
      ∀ᶠ t in nhds s, f t = (((t - s) ^ m : ℝ) : ℂ) * q t)
    (hq_cont : ContinuousAt q s)
    (hq_ne : q s ≠ 0) :
    Even m := by
  by_cases hq_re_ne : (q s).re ≠ 0
  · exact
      even_of_eventually_nonnegative_local_pow
        (s := s) (m := m) (f := fun t : ℝ => (f t).re)
        (q := fun t : ℝ => (q t).re)
        hnonneg
        (hfactor.mono fun t ht => by
          rw [ht, Complex.re_ofReal_mul])
        (Complex.continuous_re.continuousAt.comp hq_cont) hq_re_ne
  · have hq_im_ne : (q s).im ≠ 0 := by
      intro him
      exact hq_ne (Complex.ext (not_not.mp hq_re_ne) him)
    rcases lt_or_gt_of_ne hq_im_ne with hq_im_neg | hq_im_pos
    · have hq_im_eventually : ∀ᶠ t in nhds s, (q t).im < 0 := by
        have hpre :
            (fun t : ℝ => (q t).im) ⁻¹' Set.Iio 0 ∈ nhds s :=
          (Complex.continuous_im.continuousAt.comp hq_cont).preimage_mem_nhds
            (Iio_mem_nhds hq_im_neg)
        simpa [Filter.Eventually, Set.preimage, Set.Iio] using hpre
      have hp :
          ∀ᶠ t in nhds s,
            (f t).im = 0 ∧
              f t = (((t - s) ^ m : ℝ) : ℂ) * q t ∧ (q t).im < 0 :=
        hf_real.and (hfactor.and hq_im_eventually)
      rcases exists_left_right_of_eventually_nhds' hp with
        ⟨_x, y, _hxs, hsy, _hx, hy⟩
      have hysub : y - s ≠ 0 := by linarith
      have hpow_ne : (y - s) ^ m ≠ 0 := pow_ne_zero _ hysub
      have hf_im_ne : (f y).im ≠ 0 := by
        rw [hy.2.1, Complex.im_ofReal_mul]
        exact mul_ne_zero hpow_ne (ne_of_lt hy.2.2)
      exact False.elim (hf_im_ne hy.1)
    · have hq_im_eventually : ∀ᶠ t in nhds s, 0 < (q t).im := by
        have hpre :
            (fun t : ℝ => (q t).im) ⁻¹' Set.Ioi 0 ∈ nhds s :=
          (Complex.continuous_im.continuousAt.comp hq_cont).preimage_mem_nhds
            (Ioi_mem_nhds hq_im_pos)
        simpa [Filter.Eventually, Set.preimage, Set.Ioi] using hpre
      have hp :
          ∀ᶠ t in nhds s,
            (f t).im = 0 ∧
              f t = (((t - s) ^ m : ℝ) : ℂ) * q t ∧ 0 < (q t).im :=
        hf_real.and (hfactor.and hq_im_eventually)
      rcases exists_left_right_of_eventually_nhds' hp with
        ⟨_x, y, _hxs, hsy, _hx, hy⟩
      have hysub : y - s ≠ 0 := by linarith
      have hpow_ne : (y - s) ^ m ≠ 0 := pow_ne_zero _ hysub
      have hf_im_ne : (f y).im ≠ 0 := by
        rw [hy.2.1, Complex.im_ofReal_mul]
        exact mul_ne_zero hpow_ne (ne_of_gt hy.2.2)
      exact False.elim (hf_im_ne hy.1)

/-! ### Unit-circle local parametrization -/

/-- The divided slope of the unit-circle parametrization `t ↦ exp(it)` at a
phase `s`. -/
noncomputable def circleParamSlope (s : ℝ) : ℝ → ℂ :=
  dslope (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) s

/-- Local factorization of the unit-circle parametrization:
`exp(it)-exp(is)=(t-s)·circleParamSlope s t`. -/
theorem circleParam_sub_eq (s t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) - Complex.exp ((s : ℂ) * Complex.I) =
      ((t - s : ℝ) : ℂ) * circleParamSlope s t := by
  have h :=
    sub_smul_dslope (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) s t
  simpa [circleParamSlope, smul_eq_mul, sub_eq_add_neg, mul_comm] using h.symm

/-- The unit-circle parametrization is differentiable over `ℝ`. -/
theorem differentiableAt_circleParam (s : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) s := by
  have hcast : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) s := by
    simpa using (hasDerivAt_id s).ofReal_comp
  have harg : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) (Complex.I : ℂ) s := by
    simpa using hcast.mul_const Complex.I
  exact harg.cexp.differentiableAt

/-- The local slope of `t ↦ exp(it)` is continuous at the base phase. -/
theorem continuousAt_circleParamSlope (s : ℝ) :
    ContinuousAt (circleParamSlope s) s := by
  exact (continuousAt_dslope_same (f := fun t : ℝ =>
    Complex.exp ((t : ℂ) * Complex.I)) (a := s)).2
      (differentiableAt_circleParam s)

/-- The local unit-circle slope at the base phase is nonzero. -/
theorem circleParamSlope_self_ne_zero (s : ℝ) :
    circleParamSlope s s ≠ 0 := by
  have hcast : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) s := by
    simpa using (hasDerivAt_id s).ofReal_comp
  have harg : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) (Complex.I : ℂ) s := by
    simpa using hcast.mul_const Complex.I
  have hcexp :
      HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
        (Complex.exp ((s : ℂ) * Complex.I) * Complex.I) s := by
    simpa using harg.cexp
  rw [circleParamSlope, dslope_same]
  rw [hcexp.deriv]
  exact mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero

/-- The Wang root-product square root has degree at most its selected root
count. -/
theorem sourceRootProduct_natDegree_le {L : ℕ} {scale : ℂ}
    {roots : Multiset ℂ} (hroots : roots.card ≤ L) :
    (sourceRootProduct scale roots).natDegree ≤ L := by
  calc
    (sourceRootProduct scale roots).natDegree ≤
        ((roots.map fun z => (X : ℂ[X]) - C z).prod).natDegree := by
          exact Polynomial.natDegree_C_mul_le _ _
    _ = roots.card := by
          exact Polynomial.natDegree_multiset_prod_X_sub_C_eq_card roots
    _ ≤ L := hroots

/-- A nonzero Laurent polynomial of degree at most `L` has a nonzero value at
some unit-circle phase.  The proof samples the `L+1` roots of unity: otherwise
they would all be ordinary polynomial roots, impossible for degree at most `L`.
-/
theorem exists_phase_lEval_ne_zero_of_natDegree_le {L : ℕ} {F : ℂ[X]}
    (hF0 : F ≠ 0) (hdegree : F.natDegree ≤ L) :
    ∃ x : ℝ, lEval L F x ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  let N : ℕ := L + 1
  have hNpos : 0 < N := Nat.succ_pos L
  have hNne : N ≠ 0 := Nat.succ_ne_zero L
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / N)) N :=
    Complex.isPrimitiveRoot_exp N hNne
  have hsubset : (Polynomial.nthRootsFinset N (1 : ℂ)).val ⊆ F.roots := by
    intro z hz
    have hzfin : z ∈ Polynomial.nthRootsFinset N (1 : ℂ) := by
      simpa using hz
    have hzpow : z ^ N = 1 :=
      (Polynomial.mem_nthRootsFinset hNpos (1 : ℂ)).mp hzfin
    have hunit : Complex.normSq z = 1 := by
      have hnorm : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hzpow hNne
      rw [Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    rcases exists_phase_of_normSq_eq_one hunit with ⟨x, hx⟩
    have hlzero : lEval L F x = 0 := hnone x
    have heval :
        F.eval (Complex.exp ((x : ℂ) * Complex.I)) = 0 :=
      (eval_exp_eq_zero_iff_lEval_eq_zero L F x).mpr hlzero
    have hzroot : F.eval z = 0 := by
      simpa [hx] using heval
    exact (Polynomial.mem_roots hF0).mpr (by
      simpa [Polynomial.IsRoot] using hzroot)
  have hcard_le :
      (Polynomial.nthRootsFinset N (1 : ℂ)).card ≤ F.natDegree :=
    Polynomial.card_le_degree_of_subset_roots (p := F) hsubset
  have hN_le_L : N ≤ L := by
    have hcard_eq : (Polynomial.nthRootsFinset N (1 : ℂ)).card = N :=
      hprim.card_nthRootsFinset
    exact (by simpa [hcard_eq] using hcard_le.trans hdegree)
  omega

/-- The Wang selected-root product has a nonzero Laurent value at some
unit-circle phase, provided it uses at most the available Laurent budget. -/
theorem exists_phase_lEval_sourceRootProduct_ne_zero {L : ℕ}
    {roots : Multiset ℂ} (hroots : roots.card ≤ L) :
    ∃ x : ℝ, lEval L (sourceRootProduct 1 roots) x ≠ 0 :=
  exists_phase_lEval_ne_zero_of_natDegree_le
    (sourceRootProduct_one_ne_zero roots)
    (sourceRootProduct_natDegree_le (scale := 1) (roots := roots) hroots)

/-- Budgeted version of `normPolynomial_sourceRootProduct`: if the selected
nonzero reciprocal-conjugate root pairs use only `roots.card` of the available
budget, the remaining budget contributes the zero-root padding `X^(L-card)`.

This is the algebraic form needed for the degenerate bounded cases in Wang's
Laurent-complement proof, e.g. when the residual is a pure power of `X`
[WZYW23, arxiv_v3.tex:2237-2274]. -/
theorem normPolynomial_sourceRootProduct_budget (scale : ℂ) (roots : Multiset ℂ)
    (hroots0 : ∀ z ∈ roots, z ≠ 0) {L : ℕ} (hcard : roots.card ≤ L) :
    normPolynomial L (sourceRootProduct scale roots) =
      X ^ (L - roots.card) *
        sourceRootProduct
          (scale * starRingEnd ℂ scale *
            (roots.map fun z => -(starRingEnd ℂ z)).prod)
          (roots + roots.map reciprocalConj) := by
  have hbase := normPolynomial_sourceRootProduct scale roots hroots0
  have hrootDegree : (sourceRootProduct scale roots).natDegree ≤ roots.card :=
    sourceRootProduct_natDegree_le (scale := scale) (roots := roots) (le_rfl)
  have hconjDegree :
      (conjP (sourceRootProduct scale roots)).natDegree ≤ roots.card :=
    le_trans Polynomial.natDegree_map_le hrootDegree
  have hreflect :
      (conjP (sourceRootProduct scale roots)).reflect L =
        X ^ (L - roots.card) *
          (conjP (sourceRootProduct scale roots)).reflect roots.card := by
    calc
      (conjP (sourceRootProduct scale roots)).reflect L =
          (conjP (sourceRootProduct scale roots)).reflect
            (roots.card + (L - roots.card)) := by
              congr 1
              omega
      _ = X ^ (L - roots.card) *
          (conjP (sourceRootProduct scale roots)).reflect roots.card := by
            simpa using reflect_add_budget hconjDegree (L - roots.card)
  calc
    normPolynomial L (sourceRootProduct scale roots) =
        sourceRootProduct scale roots *
          (conjP (sourceRootProduct scale roots)).reflect L := rfl
    _ = sourceRootProduct scale roots *
        (X ^ (L - roots.card) *
          (conjP (sourceRootProduct scale roots)).reflect roots.card) := by
          rw [hreflect]
    _ = X ^ (L - roots.card) *
        (sourceRootProduct scale roots *
          (conjP (sourceRootProduct scale roots)).reflect roots.card) := by
          ring
    _ = X ^ (L - roots.card) *
        normPolynomial roots.card (sourceRootProduct scale roots) := by
          rw [normPolynomial]
    _ = X ^ (L - roots.card) *
        sourceRootProduct
          (scale * starRingEnd ℂ scale *
            (roots.map fun z => -(starRingEnd ℂ z)).prod)
          (roots + roots.map reciprocalConj) := by
          rw [hbase]

/-- A padded reciprocal-conjugate root selection yields Wang's source-facing
square-root certificate. -/
def PaddedReciprocalConjRootSelection.toSourceSquareRootCertificate
    {L : ℕ} {R : ℂ[X]} (h : PaddedReciprocalConjRootSelection L R) :
    SourceSquareRootCertificate L R where
  scale := h.scale
  roots := h.roots
  roots_card_le := h.roots_card_le
  factor_eq := by
    have hnorm :=
      normPolynomial_sourceRootProduct_budget h.scale h.roots h.roots_nonzero
        h.roots_card_le
    exact hnorm.trans h.padded_pair_factor_eq

/-- Convert Wang's root-product certificate to the abstract square-root
certificate consumed by the Laurent-complement adapter. -/
def SourceSquareRootCertificate.toSquareRootCertificate {L : ℕ} {R : ℂ[X]}
    (h : SourceSquareRootCertificate L R) :
    SquareRootCertificate L R where
  root := sourceRootProduct h.scale h.roots
  degree_root :=
    Polynomial.natDegree_le_iff_degree_le.mp
      (sourceRootProduct_natDegree_le h.roots_card_le)
  factor_eq := h.factor_eq

/-- Over `ℂ`, every polynomial has the source-facing full root-product
factorization used before Wang's reciprocal-conjugate root selection
[WZYW23, arxiv_v3.tex:2241-2248]. -/
def fullRootProductFactorization (R : ℂ[X]) :
    FullRootProductFactorization R where
  scale := R.leadingCoeff
  roots := R.roots
  factor_eq := by
    simpa [sourceRootProduct] using
      Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
        (IsAlgClosed.card_roots_eq_natDegree (p := R))

/-- Build a padded reciprocal-conjugate selection from selected nonzero roots,
provided the source scalar has already been square-rooted.  This isolates the
remaining analytic content of Wang's proof into the selected-root and scalar
conditions [WZYW23, arxiv_v3.tex:2249-2257]. -/
def PaddedReciprocalConjRootSelection.ofSelectedRoots {L : ℕ} {R : ℂ[X]}
    (scale : ℂ) (roots : Multiset ℂ)
    (hroots_card : roots.card ≤ L)
    (hroots_nonzero : ∀ z ∈ roots, z ≠ 0)
    (hscale :
      scale * starRingEnd ℂ scale *
        (roots.map fun z => -(starRingEnd ℂ z)).prod = R.leadingCoeff)
    (hroots :
      roots + roots.map reciprocalConj =
        R.roots.filter fun z : ℂ => z ≠ 0)
    (hzero : R.rootMultiplicity 0 = L - roots.card) :
    PaddedReciprocalConjRootSelection L R where
  scale := scale
  roots := roots
  roots_card_le := hroots_card
  roots_nonzero := hroots_nonzero
  padded_pair_factor_eq := by
    rw [hscale, hroots, ← hzero]
    calc
      X ^ R.rootMultiplicity 0 *
          sourceRootProduct R.leadingCoeff (R.roots.filter fun z : ℂ => z ≠ 0) =
        sourceRootProduct R.leadingCoeff R.roots := by
          rw [sourceRootProduct_roots_zero_nonzero_filter]
      _ = R := (fullRootProductFactorization R).factor_eq

/-- The full root-product factorization has exactly `natDegree R` root factors.
This is the bookkeeping needed before selecting one root from each
reciprocal-conjugate pair in Wang's proof [WZYW23, arxiv_v3.tex:2241-2248]. -/
theorem fullRootProductFactorization_roots_card (R : ℂ[X]) :
    (fullRootProductFactorization R).roots.card = R.natDegree := by
  exact IsAlgClosed.card_roots_eq_natDegree (p := R)

/-- The residual polynomial has the full root-product factorization that starts
Wang's Laurent-complement proof [WZYW23, arxiv_v3.tex:2241-2248]. -/
def residualPolynomialFullRootProductFactorization (L : ℕ) (F : ℂ[X]) :
    FullRootProductFactorization (residualPolynomial L F) :=
  fullRootProductFactorization (residualPolynomial L F)

/-- Cardinality form specialized to the residual polynomial. -/
theorem residualPolynomialFullRootProductFactorization_roots_card (L : ℕ)
    (F : ℂ[X]) :
    (residualPolynomialFullRootProductFactorization L F).roots.card =
      (residualPolynomial L F).natDegree := by
  exact fullRootProductFactorization_roots_card (residualPolynomial L F)

/-- `normPolynomial` evaluates to the squared absolute value of `lEval`. -/
theorem lEval_normPolynomial {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L) (x : ℝ) :
    lEval (2 * L) (normPolynomial L F) x =
      lEval L F x * starRingEnd ℂ (lEval L F x) := by
  simpa [normPolynomial] using (lEval_mul_conj (L := L) (F := F) hF x).symm

/-- `normPolynomial` is self-adjoint under coefficient conjugation and
reflection.  This is the algebraic source of the reciprocal-conjugate root
pairing in the Laurent complement proof [WZYW23, arxiv_v3.tex:2237-2274]. -/
theorem normPolynomial_conjP_reflect {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L) :
    (conjP (normPolynomial L F)).reflect (2 * L) = normPolynomial L F := by
  have hFc : (conjP F).natDegree ≤ L :=
    le_trans Polynomial.natDegree_map_le hF
  have hFr : ((conjP F).reflect L).natDegree ≤ L := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    exact coeff_reflect_eq_zero hFc hm
  have hFcr : (conjP ((conjP F).reflect L)).natDegree ≤ L :=
    le_trans Polynomial.natDegree_map_le hFr
  rw [normPolynomial, conjP_mul, two_mul]
  rw [Polynomial.reflect_mul _ _ hFc hFcr]
  rw [conjP_reflect, conjP_conjP, Polynomial.reflect_reflect]
  ring

/-- The residual `1-|F|²` is self-adjoint under coefficient conjugation and
reflection, matching the root-pair symmetry used in Wang's Laurent-complement
proof [WZYW23, arxiv_v3.tex:2237-2274]. -/
theorem residualPolynomial_conjP_reflect {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L) :
    (conjP (residualPolynomial L F)).reflect (2 * L) = residualPolynomial L F := by
  rw [residualPolynomial, conjP_sub, conjP_pow, conjP_X]
  rw [reflect_sub, normPolynomial_conjP_reflect hF]
  have hXmid : (((X : ℂ[X]) ^ L).reflect (2 * L)) = (X : ℂ[X]) ^ L := by
    rw [Polynomial.reflect_monomial]
    congr 1
    rw [Polynomial.revAt_le (by omega)]
    omega
  rw [hXmid]

/-- The residual polynomial has degree at most its reflected Laurent budget. -/
theorem residualPolynomial_natDegree_le {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L) :
    (residualPolynomial L F).natDegree ≤ 2 * L := by
  have hnormDegree : (normPolynomial L F).natDegree ≤ 2 * L := by
    have hFc : (conjP F).natDegree ≤ L :=
      le_trans Polynomial.natDegree_map_le hF
    have hFr : ((conjP F).reflect L).natDegree ≤ L := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      exact coeff_reflect_eq_zero hFc hm
    calc
      (normPolynomial L F).natDegree =
          (F * (conjP F).reflect L).natDegree := rfl
      _ ≤ F.natDegree + ((conjP F).reflect L).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ L + L := Nat.add_le_add hF hFr
      _ = 2 * L := by omega
  calc
    (residualPolynomial L F).natDegree =
        (X ^ L - normPolynomial L F).natDegree := rfl
    _ ≤ max ((X : ℂ[X]) ^ L).natDegree (normPolynomial L F).natDegree :=
        Polynomial.natDegree_sub_le _ _
    _ ≤ 2 * L := by
        rw [Polynomial.natDegree_X_pow]
        exact max_le (by omega) hnormDegree

/-- A nonzero Laurent self-adjoint polynomial has exactly the zero-root padding
forced by its reflected budget.  This is the bookkeeping behind the missing
high-degree terms in Wang's root-product proof [WZYW23, arxiv_v3.tex:2241-2257]. -/
theorem rootMultiplicity_zero_eq_budget_sub_natDegree_of_conjP_reflect
    {N : ℕ} {R : ℂ[X]} (hRdeg : R.natDegree ≤ N)
    (hself : (conjP R).reflect N = R) (hR0 : R ≠ 0) :
    R.rootMultiplicity 0 = N - R.natDegree := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree']
  apply le_antisymm
  · apply Polynomial.natTrailingDegree_le_of_ne_zero
    calc
      R.coeff (N - R.natDegree) =
          ((conjP R).reflect N).coeff (N - R.natDegree) := by rw [hself]
      _ = (conjP R).coeff R.natDegree := by
          rw [coeff_reflect_of_le (by omega)]
          congr 1
          omega
      _ ≠ 0 := by
          rw [conjP_coeff]
          have hlead : R.coeff R.natDegree ≠ 0 := by
            change R.leadingCoeff ≠ 0
            exact Polynomial.leadingCoeff_ne_zero.mpr hR0
          exact star_ne_zero.mpr
            hlead
  · apply Polynomial.le_natTrailingDegree hR0
    intro m hm
    calc
      R.coeff m = ((conjP R).reflect N).coeff m := by rw [hself]
      _ = (conjP R).coeff (N - m) := by
          rw [coeff_reflect_of_le (by omega)]
      _ = 0 := by
          rw [conjP_coeff]
          have hgt : R.natDegree < N - m := by omega
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt, map_zero]

/-- The residual polynomial's zero-root multiplicity is exactly the reflected
budget slack. -/
theorem residualPolynomial_rootMultiplicity_zero_eq_budget_sub_natDegree
    {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L)
    (hres0 : residualPolynomial L F ≠ 0) :
    (residualPolynomial L F).rootMultiplicity 0 =
      2 * L - (residualPolynomial L F).natDegree := by
  exact rootMultiplicity_zero_eq_budget_sub_natDegree_of_conjP_reflect
    (residualPolynomial_natDegree_le hF) (residualPolynomial_conjP_reflect hF) hres0

/-- Roots of a self-adjoint Laurent polynomial are closed under reciprocal
conjugation.  This is the Lean form of Wang's inverse-conjugate root pairing
for the residual polynomial [WZYW23, arxiv_v3.tex:2241-2248]. -/
theorem eval_reciprocal_conj_eq_zero_of_conjP_reflect
    {N : ℕ} {R : ℂ[X]} (hR : R.natDegree ≤ N)
    (hself : (conjP R).reflect N = R) {z : ℂ}
    (hz0 : z ≠ 0) (hz : R.eval z = 0) :
    R.eval (reciprocalConj z) = 0 := by
  change R.eval (starRingEnd ℂ z)⁻¹ = 0
  have hconj0 : starRingEnd ℂ z ≠ 0 := by
    simpa [star_ne_zero] using hz0
  have hconjDegree : (conjP R).natDegree ≤ N :=
    le_trans Polynomial.natDegree_map_le hR
  calc
    R.eval (starRingEnd ℂ z)⁻¹ =
        ((conjP R).reflect N).eval (starRingEnd ℂ z)⁻¹ := by
          rw [hself]
    _ = ((starRingEnd ℂ z)⁻¹) ^ N *
        (conjP R).eval (((starRingEnd ℂ z)⁻¹)⁻¹) := by
          rw [eval_reflect hconjDegree (inv_ne_zero hconj0)]
    _ = ((starRingEnd ℂ z)⁻¹) ^ N *
        (conjP R).eval (starRingEnd ℂ z) := by
          rw [inv_inv]
    _ = ((starRingEnd ℂ z)⁻¹) ^ N * starRingEnd ℂ (R.eval z) := by
          rw [conjP_eval_conj]
    _ = 0 := by
          rw [hz, map_zero, mul_zero]

/-- Root-set form of `eval_reciprocal_conj_eq_zero_of_conjP_reflect`. -/
theorem mem_roots_reciprocal_conj_of_conjP_reflect
    {N : ℕ} {R : ℂ[X]} (hR : R.natDegree ≤ N)
    (hself : (conjP R).reflect N = R) (hR0 : R ≠ 0) {z : ℂ}
    (hz0 : z ≠ 0) (hz : z ∈ R.roots) :
    reciprocalConj z ∈ R.roots := by
  exact (Polynomial.mem_roots hR0).mpr
    (eval_reciprocal_conj_eq_zero_of_conjP_reflect hR hself hz0
      ((Polynomial.mem_roots hR0).mp hz))

/-- Nonzero roots of a self-adjoint Laurent polynomial are equivalent under
the inverse-conjugate pairing. -/
theorem mem_roots_reciprocal_conj_iff_of_conjP_reflect
    {N : ℕ} {R : ℂ[X]} (hR : R.natDegree ≤ N)
    (hself : (conjP R).reflect N = R) (hR0 : R ≠ 0) {z : ℂ}
    (hz0 : z ≠ 0) :
    reciprocalConj z ∈ R.roots ↔ z ∈ R.roots := by
  constructor
  · intro hz
    have hnonzero : reciprocalConj z ≠ 0 := reciprocalConj_ne_zero hz0
    have hmem :=
      mem_roots_reciprocal_conj_of_conjP_reflect hR hself hR0 hnonzero hz
    simpa [reciprocalConj_involutive z] using hmem
  · exact mem_roots_reciprocal_conj_of_conjP_reflect hR hself hR0 hz0

/-- Reflection plus coefficient conjugation preserves root multiplicity at the
inverse-conjugate root.  This is the multiplicity form of Wang's root-pairing
identity `e^{ix/2}-ξ = -e^{ix/2}ξ(e^{-ix/2}-1/ξ*)`
[WZYW23, arxiv_v3.tex:2249-2251]. -/
theorem reflect_conjP_rootMultiplicity
    {P : ℂ[X]} {N : ℕ} (hPdeg : P.natDegree ≤ N) (hP0 : P ≠ 0)
    {z : ℂ} (hz0 : z ≠ 0) :
    ((conjP P).reflect N).rootMultiplicity (reciprocalConj z) =
      P.rootMultiplicity z := by
  classical
  let m := P.rootMultiplicity z
  rcases Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP0 z with
    ⟨q, hfactor, hq_not_dvd⟩
  have hfactor_m : P = ((X : ℂ[X]) - C z) ^ m * q := by
    simpa [m] using hfactor
  have hq0 : q ≠ 0 := by
    intro hq
    rw [hq, mul_zero] at hfactor_m
    exact hP0 hfactor_m
  have hpowDeg : (((X : ℂ[X]) - C z) ^ m).natDegree = m := by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
    simp
  have hqdeg : q.natDegree ≤ N - m := by
    have hmul :
        (((X : ℂ[X]) - C z) ^ m * q).natDegree = m + q.natDegree := by
      rw [Polynomial.natDegree_mul]
      · rw [hpowDeg]
      · exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero z)
      · exact hq0
    have hPdeg' : (((X : ℂ[X]) - C z) ^ m * q).natDegree ≤ N := by
      simpa [hfactor_m] using hPdeg
    rw [hmul] at hPdeg'
    omega
  have hq_eval_ne : q.eval z ≠ 0 := by
    intro hzero
    have hroot : q.IsRoot z := by
      rw [Polynomial.IsRoot.def]
      exact hzero
    exact hq_not_dvd ((Polynomial.dvd_iff_isRoot).mpr hroot)
  have hconj_q_eval_ne :
      (conjP q).eval (starRingEnd ℂ z) ≠ 0 := by
    rw [conjP_eval_conj]
    simpa using (star_ne_zero.mpr hq_eval_ne)
  have hreflect_q_eval_ne :
      ((conjP q).reflect (N - m)).eval (reciprocalConj z) ≠ 0 := by
    rw [conjP]
    rw [eval_reflect (le_trans Polynomial.natDegree_map_le hqdeg)
      (reciprocalConj_ne_zero hz0)]
    rw [reciprocalConj, inv_inv]
    exact mul_ne_zero (pow_ne_zero _ (reciprocalConj_ne_zero hz0)) hconj_q_eval_ne
  have hP_natDegree : P.natDegree = m + q.natDegree := by
    rw [hfactor_m, Polynomial.natDegree_mul, hpowDeg]
    · exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero z)
    · exact hq0
  have hm_le_N : m ≤ N := by
    have hm_le_deg : m ≤ P.natDegree := by
      rw [hP_natDegree]
      omega
    exact le_trans hm_le_deg hPdeg
  have hNsplit : m + (N - m) = N := Nat.add_sub_of_le hm_le_N
  have hpow_conj_deg :
      (conjP (((X : ℂ[X]) - C z) ^ m)).natDegree ≤ m := by
    calc
      (conjP (((X : ℂ[X]) - C z) ^ m)).natDegree ≤
          (((X : ℂ[X]) - C z) ^ m).natDegree :=
        Polynomial.natDegree_map_le
      _ = m := hpowDeg
  have hq_conj_deg : (conjP q).natDegree ≤ N - m :=
    le_trans Polynomial.natDegree_map_le hqdeg
  let a := reciprocalConj z
  let c : ℂ := (-(starRingEnd ℂ z)) ^ m
  let qref : ℂ[X] := (conjP q).reflect (N - m)
  have hc0 : c ≠ 0 := by
    exact pow_ne_zero _ (neg_ne_zero.mpr (star_ne_zero.mpr hz0))
  have hqref_eval_ne : qref.eval a ≠ 0 := by
    simpa [qref, a] using hreflect_q_eval_ne
  have hqref0 : qref ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.eval_zero] at hqref_eval_ne
    exact hqref_eval_ne rfl
  have hreflect_factor :
      ((conjP P).reflect N) =
        C c * ((X : ℂ[X]) - C a) ^ m * qref := by
    rw [← hNsplit, hfactor_m, conjP_mul]
    rw [Polynomial.reflect_mul _ _ hpow_conj_deg hq_conj_deg]
    rw [reflect_conjP_X_sub_C_pow z m hz0]
  have hreflect_factor_comm :
      ((conjP P).reflect N) =
        (C c * qref) * ((X : ℂ[X]) - C a) ^ m := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hreflect_factor
  have hbase0 : C c * qref ≠ 0 := by
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hc0) hqref0
  have hbase_not_root : ¬ Polynomial.IsRoot (C c * qref) a := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_mul, Polynomial.eval_C]
    exact mul_ne_zero hc0 hqref_eval_ne
  have hbase_mult_zero : (C c * qref).rootMultiplicity a = 0 :=
    Polynomial.rootMultiplicity_eq_zero hbase_not_root
  calc
    ((conjP P).reflect N).rootMultiplicity a =
        ((C c * qref) * ((X : ℂ[X]) - C a) ^ m).rootMultiplicity a := by
          rw [hreflect_factor_comm]
    _ = (C c * qref).rootMultiplicity a + m := by
          exact Polynomial.rootMultiplicity_mul_X_sub_C_pow hbase0
    _ = m := by
          rw [hbase_mult_zero, zero_add]

/-- Self-adjoint Laurent polynomials have equal reciprocal-conjugate root
multiplicities.  This is the multiplicity-strengthened form of Wang's
inverse-conjugate root pairing [WZYW23, arxiv_v3.tex:2241-2248]. -/
theorem rootMultiplicity_reciprocalConj_eq_of_conjP_reflect
    {N : ℕ} {R : ℂ[X]} (hR : R.natDegree ≤ N)
    (hself : (conjP R).reflect N = R) (hR0 : R ≠ 0) {z : ℂ}
    (hz0 : z ≠ 0) :
    R.rootMultiplicity (reciprocalConj z) = R.rootMultiplicity z := by
  calc
    R.rootMultiplicity (reciprocalConj z) =
        ((conjP R).reflect N).rootMultiplicity (reciprocalConj z) := by
          rw [hself]
    _ = R.rootMultiplicity z := reflect_conjP_rootMultiplicity hR hR0 hz0

/-- If reciprocal-conjugate roots have equal multiplicity, then the multiset
of nonzero roots is invariant under Wang's inverse-conjugate pairing.  This
isolates the finite multiset bookkeeping needed after the multiplicity proof
for [WZYW23, arxiv_v3.tex:2241-2248]. -/
theorem nonzero_roots_map_reciprocalConj_eq_of_rootMultiplicity_eq
    (R : ℂ[X])
    (hmult : ∀ z : ℂ, z ≠ 0 →
      R.rootMultiplicity (reciprocalConj z) = R.rootMultiplicity z) :
    ((R.roots.filter fun z : ℂ => z ≠ 0).map reciprocalConj) =
      (R.roots.filter fun z : ℂ => z ≠ 0) := by
  classical
  ext z
  by_cases hz0 : z = 0
  · subst z
    have hleft :
        ((R.roots.filter fun z : ℂ => z ≠ 0).map reciprocalConj).count 0 = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      rcases Multiset.mem_map.mp hmem with ⟨w, hw, hw0⟩
      have hnz : w ≠ 0 := (Multiset.mem_filter.mp hw).2
      exact reciprocalConj_ne_zero hnz hw0
    have hright :
        (R.roots.filter fun z : ℂ => z ≠ 0).count 0 = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      exact (Multiset.mem_filter.mp hmem).2 rfl
    rw [hleft, hright]
  · calc
      ((R.roots.filter fun z : ℂ => z ≠ 0).map reciprocalConj).count z =
          ((R.roots.filter fun z : ℂ => z ≠ 0).map reciprocalConj).count
            (reciprocalConj (reciprocalConj z)) := by
            rw [reciprocalConj_involutive]
      _ = (R.roots.filter fun z : ℂ => z ≠ 0).count (reciprocalConj z) := by
            rw [Multiset.count_map_eq_count' reciprocalConj
              (R.roots.filter fun z : ℂ => z ≠ 0) reciprocalConj_injective]
      _ = R.roots.count (reciprocalConj z) := by
            simpa using
              (Multiset.count_filter_of_pos
                (s := R.roots) (a := reciprocalConj z)
                (p := fun w : ℂ => w ≠ 0) (reciprocalConj_ne_zero hz0))
      _ = R.rootMultiplicity (reciprocalConj z) := by
            rw [Polynomial.count_roots]
      _ = R.rootMultiplicity z := hmult z hz0
      _ = R.roots.count z := by
            rw [Polynomial.count_roots]
      _ = (R.roots.filter fun z : ℂ => z ≠ 0).count z := by
            simpa using
              (Multiset.count_filter_of_pos
                (s := R.roots) (a := z) (p := fun w : ℂ => w ≠ 0) hz0).symm

/-- The residual roots used by Wang's Laurent complement proof are closed under
`z ↦ 1 / z*` [WZYW23, arxiv_v3.tex:2241-2248]. -/
theorem residualPolynomial_eval_reciprocal_conj_eq_zero
    {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L) {z : ℂ}
    (hz0 : z ≠ 0) (hz : (residualPolynomial L F).eval z = 0) :
    (residualPolynomial L F).eval (reciprocalConj z) = 0 := by
  have hnormDegree : (normPolynomial L F).natDegree ≤ 2 * L := by
    have hFc : (conjP F).natDegree ≤ L :=
      le_trans Polynomial.natDegree_map_le hF
    have hFr : ((conjP F).reflect L).natDegree ≤ L :=
      Polynomial.natDegree_le_iff_degree_le.mpr <|
        (Polynomial.degree_le_iff_coeff_zero _ _).mpr fun m hm =>
          coeff_reflect_eq_zero hFc (by exact_mod_cast hm)
    calc
      (normPolynomial L F).natDegree =
          (F * (conjP F).reflect L).natDegree := rfl
      _ ≤ F.natDegree + ((conjP F).reflect L).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ L + L := Nat.add_le_add hF hFr
      _ = 2 * L := by omega
  have hRdegree : (residualPolynomial L F).natDegree ≤ 2 * L := by
    calc
      (residualPolynomial L F).natDegree =
          (X ^ L - normPolynomial L F).natDegree := rfl
      _ ≤ max ((X : ℂ[X]) ^ L).natDegree (normPolynomial L F).natDegree :=
          Polynomial.natDegree_sub_le _ _
      _ ≤ 2 * L := by
          rw [Polynomial.natDegree_X_pow]
          exact max_le (by omega) hnormDegree
  exact eval_reciprocal_conj_eq_zero_of_conjP_reflect hRdegree
    (residualPolynomial_conjP_reflect hF) hz0 hz

/-- Root-set form of `residualPolynomial_eval_reciprocal_conj_eq_zero`. -/
theorem residualPolynomial_mem_roots_reciprocal_conj
    {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L)
    (hres0 : residualPolynomial L F ≠ 0) {z : ℂ}
    (hz0 : z ≠ 0) (hz : z ∈ (residualPolynomial L F).roots) :
    reciprocalConj z ∈ (residualPolynomial L F).roots := by
  exact (Polynomial.mem_roots hres0).mpr
    (residualPolynomial_eval_reciprocal_conj_eq_zero hF hz0
      ((Polynomial.mem_roots hres0).mp hz))

/-- Nonzero residual roots are equivalent under inverse-conjugation. -/
theorem residualPolynomial_mem_roots_reciprocal_conj_iff
    {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L)
    (hres0 : residualPolynomial L F ≠ 0) {z : ℂ}
    (hz0 : z ≠ 0) :
    reciprocalConj z ∈ (residualPolynomial L F).roots ↔
      z ∈ (residualPolynomial L F).roots := by
  constructor
  · intro hz
    have hnonzero : reciprocalConj z ≠ 0 := reciprocalConj_ne_zero hz0
    have hmem :=
      residualPolynomial_mem_roots_reciprocal_conj hF hres0 hnonzero hz
    simpa [reciprocalConj_involutive z] using hmem
  · exact residualPolynomial_mem_roots_reciprocal_conj hF hres0 hz0

/-- Residual root multiplicities are invariant under Wang's inverse-conjugate
root pairing [WZYW23, arxiv_v3.tex:2241-2251]. -/
theorem residualPolynomial_rootMultiplicity_reciprocalConj_eq
    {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L) {z : ℂ}
    (hz0 : z ≠ 0) :
    (residualPolynomial L F).rootMultiplicity (reciprocalConj z) =
      (residualPolynomial L F).rootMultiplicity z := by
  by_cases hres0 : residualPolynomial L F = 0
  · simp [hres0]
  · exact rootMultiplicity_reciprocalConj_eq_of_conjP_reflect
      (residualPolynomial_natDegree_le hF) (residualPolynomial_conjP_reflect hF)
      hres0 hz0

/-- The nonzero residual roots, counted with multiplicity, are invariant under
Wang's inverse-conjugate root pairing [WZYW23, arxiv_v3.tex:2241-2251]. -/
theorem residualPolynomial_nonzero_roots_map_reciprocalConj_eq
    {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L) :
    (((residualPolynomial L F).roots.filter fun z : ℂ => z ≠ 0).map reciprocalConj) =
      ((residualPolynomial L F).roots.filter fun z : ℂ => z ≠ 0) :=
  nonzero_roots_map_reciprocalConj_eq_of_rootMultiplicity_eq
    (residualPolynomial L F)
    (fun z hz0 =>
      residualPolynomial_rootMultiplicity_reciprocalConj_eq (L := L) (F := F) (z := z) hF hz0)

/-- Count form of reciprocal-conjugate invariance for the nonzero residual
roots. -/
theorem residualPolynomial_nonzero_roots_count_reciprocalConj_eq
    {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L) {z : ℂ} (hz0 : z ≠ 0) :
    (((residualPolynomial L F).roots.filter fun w : ℂ => w ≠ 0).count (reciprocalConj z)) =
      (((residualPolynomial L F).roots.filter fun w : ℂ => w ≠ 0).count z) := by
  classical
  have hrec0 : reciprocalConj z ≠ 0 := reciprocalConj_ne_zero hz0
  rw [Multiset.count_filter_of_pos
      (s := (residualPolynomial L F).roots) (a := reciprocalConj z)
      (p := fun w : ℂ => w ≠ 0) hrec0,
    Multiset.count_filter_of_pos
      (s := (residualPolynomial L F).roots) (a := z)
      (p := fun w : ℂ => w ≠ 0) hz0,
    Polynomial.count_roots, Polynomial.count_roots]
  exact residualPolynomial_rootMultiplicity_reciprocalConj_eq
    (L := L) (F := F) (z := z) hF hz0

/-- Wang's canonical half-root selection for reciprocal-conjugate pairs.  It
selects every nonzero root strictly inside the unit circle and half of each
unit-circle multiplicity.  The roots outside the unit circle are then supplied
by the reflected image of the selected inside roots [WZYW23,
arxiv_v3.tex:2241-2257]. -/
def selectedReciprocalConjRoots (s : Multiset ℂ) : Multiset ℂ :=
  (s.filter fun z : ℂ => z ≠ 0 ∧ Complex.normSq z < 1) +
    ((s.filter fun z : ℂ => z ≠ 0 ∧ Complex.normSq z = 1).dedup.bind
      fun z => Multiset.replicate (s.count z / 2) z)

/-- The canonical half-root selection never includes the zero root. -/
theorem selectedReciprocalConjRoots_nonzero {s : Multiset ℂ} {z : ℂ}
    (hz : z ∈ selectedReciprocalConjRoots s) :
    z ≠ 0 := by
  rw [selectedReciprocalConjRoots, Multiset.mem_add] at hz
  rcases hz with hz | hz
  · exact (Multiset.mem_filter.mp hz).2.1
  · rcases Multiset.mem_bind.mp hz with ⟨w, hw, hzw⟩
    rcases Multiset.mem_replicate.mp hzw with ⟨_, rfl⟩
    exact (Multiset.mem_filter.mp (Multiset.mem_dedup.mp hw)).2.1

/-- The scalar product over selected Wang roots is nonzero. -/
theorem selectedReciprocalConjRoots_neg_conj_prod_ne_zero (s : Multiset ℂ) :
    ((selectedReciprocalConjRoots s).map
      (fun z => -(starRingEnd ℂ z))).prod ≠ 0 := by
  apply Multiset.prod_ne_zero
  intro hzero_mem
  rcases Multiset.mem_map.mp hzero_mem with ⟨z, hz, hzero⟩
  have hz0 : z ≠ 0 := selectedReciprocalConjRoots_nonzero hz
  exact hz0 (star_eq_zero.mp (neg_eq_zero.mp hzero))

/-- Wang's source scalar quotient for the selected reciprocal-conjugate roots:
the proof of Laurent-complement existence shows this quotient is a nonnegative
real number before taking its square root [WZYW23, arxiv_v3.tex:2253-2257]. -/
noncomputable def sourceScalarQuotient (R : ℂ[X]) : ℂ :=
  R.leadingCoeff /
    ((selectedReciprocalConjRoots (R.roots.filter fun z : ℂ => z ≠ 0)).map
      (fun z => -(starRingEnd ℂ z))).prod

/-- The selected-root denominator in Wang's source scalar quotient is nonzero. -/
theorem sourceScalarQuotient_denominator_ne_zero (R : ℂ[X]) :
    ((selectedReciprocalConjRoots (R.roots.filter fun z : ℂ => z ≠ 0)).map
      (fun z => -(starRingEnd ℂ z))).prod ≠ 0 :=
  selectedReciprocalConjRoots_neg_conj_prod_ne_zero
    (R.roots.filter fun z : ℂ => z ≠ 0)

/-- Sum a single nonzero `if` branch over a nodup multiset. -/
theorem Multiset.sum_map_if_eq_of_nodup {α : Type*} [DecidableEq α]
    (s : Multiset α) (hs : s.Nodup) (a : α) (f : α → ℕ) :
    (s.map fun x => if x = a then f x else 0).sum =
      if a ∈ s then f a else 0 := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | cons b s ih =>
      rw [Multiset.nodup_cons] at hs
      rcases hs with ⟨hb_not_mem, hs⟩
      by_cases hba : b = a
      · subst b
        have htail := ih hs
        have ha_not_mem : a ∉ s := hb_not_mem
        simp [ha_not_mem, htail]
      · have htail := ih hs
        have hab : a ≠ b := by
          intro hab
          exact hba hab.symm
        simp [hba, hab, htail]

/-- Unit-circle roots are selected with half of their multiplicity.  The
evenness of these multiplicities is proved separately from boundedness of the
residual on the unit circle. -/
theorem selectedReciprocalConjRoots_count_of_normSq_eq_one
    (s : Multiset ℂ) {z : ℂ} (hunit : Complex.normSq z = 1) :
    (selectedReciprocalConjRoots s).count z = s.count z / 2 := by
  classical
  have hz0 : z ≠ 0 := by
    intro hz
    subst z
    norm_num [Complex.normSq] at hunit
  have hnotInside : ¬(z ≠ 0 ∧ Complex.normSq z < 1) := by
    intro h
    linarith
  have hinside_count :
      Multiset.count z
          (Multiset.filter (fun w : ℂ => w ≠ 0 ∧ Complex.normSq w < 1) s) = 0 :=
    Multiset.count_filter_of_neg hnotInside
  let unitRoots := Multiset.filter (fun w : ℂ => w ≠ 0 ∧ Complex.normSq w = 1) s
  have hsum :=
    Multiset.sum_map_if_eq_of_nodup unitRoots.dedup (Multiset.nodup_dedup unitRoots) z
      (fun w => s.count w / 2)
  rw [selectedReciprocalConjRoots, Multiset.count_add, hinside_count, zero_add]
  rw [Multiset.count_bind]
  by_cases hzmem : z ∈ s
  · have hzmem_unit : z ∈ unitRoots.dedup := by
      rw [Multiset.mem_dedup, Multiset.mem_filter]
      exact ⟨hzmem, hz0, hunit⟩
    simp [unitRoots, Multiset.count_replicate, hsum, hzmem_unit]
  · have hcount_zero : s.count z = 0 := by
      exact Multiset.count_eq_zero.mpr hzmem
    have hznot_mem_unit : z ∉ unitRoots.dedup := by
      rw [Multiset.mem_dedup, Multiset.mem_filter]
      intro h
      exact hzmem h.1
    simp [unitRoots, Multiset.count_replicate, hsum, hznot_mem_unit, hcount_zero]

/-- Nonzero roots strictly inside the unit circle are selected with full
multiplicity. -/
theorem selectedReciprocalConjRoots_count_of_normSq_lt_one
    (s : Multiset ℂ) {z : ℂ} (hz0 : z ≠ 0) (hinside : Complex.normSq z < 1) :
    (selectedReciprocalConjRoots s).count z = s.count z := by
  classical
  have hnotUnit : Complex.normSq z ≠ 1 := by
    linarith
  have hinside_count :
      Multiset.count z
          (Multiset.filter (fun w : ℂ => w ≠ 0 ∧ Complex.normSq w < 1) s) =
        s.count z :=
    Multiset.count_filter_of_pos ⟨hz0, hinside⟩
  let unitRoots := Multiset.filter (fun w : ℂ => w ≠ 0 ∧ Complex.normSq w = 1) s
  have hsum :=
    Multiset.sum_map_if_eq_of_nodup unitRoots.dedup (Multiset.nodup_dedup unitRoots) z
      (fun w => s.count w / 2)
  have hznot_mem_unit : z ∉ unitRoots.dedup := by
    rw [Multiset.mem_dedup, Multiset.mem_filter]
    intro h
    exact hnotUnit h.2.2
  rw [selectedReciprocalConjRoots, Multiset.count_add, hinside_count]
  rw [Multiset.count_bind]
  simp [unitRoots, Multiset.count_replicate, hsum, hznot_mem_unit]

/-- Roots strictly outside the unit circle are not selected directly; they are
supplied by reciprocal-conjugating the selected inside roots. -/
theorem selectedReciprocalConjRoots_count_of_one_lt_normSq
    (s : Multiset ℂ) {z : ℂ} (houtside : 1 < Complex.normSq z) :
    (selectedReciprocalConjRoots s).count z = 0 := by
  classical
  have hz0 : z ≠ 0 := by
    intro hz
    subst z
    norm_num [Complex.normSq] at houtside
  have hnotInside : ¬(z ≠ 0 ∧ Complex.normSq z < 1) := by
    intro h
    linarith
  have hnotUnit : Complex.normSq z ≠ 1 := by
    linarith
  have hinside_count :
      Multiset.count z
          (Multiset.filter (fun w : ℂ => w ≠ 0 ∧ Complex.normSq w < 1) s) = 0 :=
    Multiset.count_filter_of_neg hnotInside
  let unitRoots := Multiset.filter (fun w : ℂ => w ≠ 0 ∧ Complex.normSq w = 1) s
  have hsum :=
    Multiset.sum_map_if_eq_of_nodup unitRoots.dedup (Multiset.nodup_dedup unitRoots) z
      (fun w => s.count w / 2)
  have hznot_mem_unit : z ∉ unitRoots.dedup := by
    rw [Multiset.mem_dedup, Multiset.mem_filter]
    intro h
    exact hnotUnit h.2.2
  rw [selectedReciprocalConjRoots, Multiset.count_add, hinside_count, zero_add]
  rw [Multiset.count_bind]
  simp [unitRoots, Multiset.count_replicate, hsum, hznot_mem_unit]

/-- Count form of Wang's selected root pairing away from zero.  Once unit-circle
roots are known to have even multiplicity, the selected roots and their
inverse-conjugates recover every nonzero root with multiplicity. -/
theorem selectedReciprocalConjRoots_add_map_count_eq
    (s : Multiset ℂ)
    (hmult : ∀ z : ℂ, z ≠ 0 → s.count (reciprocalConj z) = s.count z)
    (hunit_even : ∀ z : ℂ, z ≠ 0 → Complex.normSq z = 1 → Even (s.count z))
    {z : ℂ} (hz0 : z ≠ 0) :
    (selectedReciprocalConjRoots s + (selectedReciprocalConjRoots s).map reciprocalConj).count z =
      s.count z := by
  classical
  have hmap_count :
      ((selectedReciprocalConjRoots s).map reciprocalConj).count z =
        (selectedReciprocalConjRoots s).count (reciprocalConj z) := by
    calc
      ((selectedReciprocalConjRoots s).map reciprocalConj).count z =
          ((selectedReciprocalConjRoots s).map reciprocalConj).count
            (reciprocalConj (reciprocalConj z)) := by
              rw [reciprocalConj_involutive]
      _ = (selectedReciprocalConjRoots s).count (reciprocalConj z) := by
              rw [Multiset.count_map_eq_count' reciprocalConj
                (selectedReciprocalConjRoots s) reciprocalConj_injective]
  rw [Multiset.count_add, hmap_count]
  by_cases hinside : Complex.normSq z < 1
  · have houtside_rec :
        1 < Complex.normSq (reciprocalConj z) :=
      one_lt_normSq_reciprocalConj_of_normSq_lt_one hz0 hinside
    rw [selectedReciprocalConjRoots_count_of_normSq_lt_one s hz0 hinside,
      selectedReciprocalConjRoots_count_of_one_lt_normSq s houtside_rec]
    omega
  · by_cases hunit : Complex.normSq z = 1
    · have hrec : reciprocalConj z = z :=
        reciprocalConj_eq_self_of_normSq_eq_one hunit
      rw [hrec, selectedReciprocalConjRoots_count_of_normSq_eq_one s hunit]
      rcases hunit_even z hz0 hunit with ⟨k, hk⟩
      omega
    · have houtside : 1 < Complex.normSq z := by
        have hneq : Complex.normSq z ≠ 1 := hunit
        rcases lt_or_gt_of_ne hneq with hlt | hgt
        · exact False.elim (hinside hlt)
        · exact hgt
      have hinside_rec :
          Complex.normSq (reciprocalConj z) < 1 :=
        normSq_reciprocalConj_lt_one_of_one_lt_normSq houtside
      have hrec0 : reciprocalConj z ≠ 0 := reciprocalConj_ne_zero hz0
      rw [selectedReciprocalConjRoots_count_of_one_lt_normSq s houtside,
        selectedReciprocalConjRoots_count_of_normSq_lt_one s hrec0 hinside_rec]
      rw [zero_add, hmult z hz0]

/-- Multiset form of Wang's nonzero reciprocal-conjugate root selection. -/
theorem selectedReciprocalConjRoots_add_map_eq_nonzero_filter
    (s : Multiset ℂ)
    (hmult : ∀ z : ℂ, z ≠ 0 → s.count (reciprocalConj z) = s.count z)
    (hunit_even : ∀ z : ℂ, z ≠ 0 → Complex.normSq z = 1 → Even (s.count z)) :
    selectedReciprocalConjRoots s + (selectedReciprocalConjRoots s).map reciprocalConj =
      s.filter fun z : ℂ => z ≠ 0 := by
  classical
  ext z
  by_cases hz0 : z = 0
  · subst z
    have hsel0 : (selectedReciprocalConjRoots s).count 0 = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      exact selectedReciprocalConjRoots_nonzero hmem rfl
    have hmap0 : ((selectedReciprocalConjRoots s).map reciprocalConj).count 0 = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      rcases Multiset.mem_map.mp hmem with ⟨w, hw, hw0⟩
      exact reciprocalConj_ne_zero (selectedReciprocalConjRoots_nonzero hw) hw0
    rw [Multiset.count_add, hsel0, hmap0]
    simp
  · rw [selectedReciprocalConjRoots_add_map_count_eq s hmult hunit_even hz0]
    exact (Multiset.count_filter_of_pos
      (s := s) (a := z) (p := fun w : ℂ => w ≠ 0) hz0).symm

/-- Selected residual roots recover the nonzero residual roots, once the
unit-circle residual multiplicities are known to be even. -/
theorem residualPolynomial_selected_roots_add_map_eq_nonzero_roots
    {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L)
    (hunit_even : ∀ z : ℂ, z ≠ 0 → Complex.normSq z = 1 →
      Even ((residualPolynomial L F).roots.count z)) :
    selectedReciprocalConjRoots
        ((residualPolynomial L F).roots.filter fun z : ℂ => z ≠ 0) +
      (selectedReciprocalConjRoots
        ((residualPolynomial L F).roots.filter fun z : ℂ => z ≠ 0)).map reciprocalConj =
      ((residualPolynomial L F).roots.filter fun z : ℂ => z ≠ 0) := by
  classical
  have h :=
    selectedReciprocalConjRoots_add_map_eq_nonzero_filter
      ((residualPolynomial L F).roots.filter fun z : ℂ => z ≠ 0)
      (fun z hz0 =>
        residualPolynomial_nonzero_roots_count_reciprocalConj_eq
          (L := L) (F := F) hF hz0)
      (fun z hz0 hunit => by
        rw [Multiset.count_filter_of_pos
          (s := (residualPolynomial L F).roots) (a := z)
          (p := fun w : ℂ => w ≠ 0) hz0]
        exact hunit_even z hz0 hunit)
  simpa [Multiset.filter_filter, and_assoc] using h

/-- Residual selected roots give a padded reciprocal-conjugate selection once
the unit-circle multiplicities are even and the source scalar has been
square-rooted.  This is the compact algebraic endpoint of Wang's root
classification step before constructing the Laurent complement
[WZYW23, arxiv_v3.tex:2249-2257]. -/
def residualPolynomialPaddedSelectionOfUnitCircleEvenAndScale
    {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L)
    (hres0 : residualPolynomial L F ≠ 0)
    (hunit_even : ∀ z : ℂ, z ≠ 0 → Complex.normSq z = 1 →
      Even ((residualPolynomial L F).roots.count z))
    (scale : ℂ)
    (hscale :
      scale * starRingEnd ℂ scale *
        ((selectedReciprocalConjRoots
          ((residualPolynomial L F).roots.filter fun z : ℂ => z ≠ 0)).map
            fun z => -(starRingEnd ℂ z)).prod =
        (residualPolynomial L F).leadingCoeff) :
    PaddedReciprocalConjRootSelection L (residualPolynomial L F) := by
  classical
  let R : ℂ[X] := residualPolynomial L F
  let roots : Multiset ℂ :=
    selectedReciprocalConjRoots (R.roots.filter fun z : ℂ => z ≠ 0)
  have hroots :
      roots + roots.map reciprocalConj =
        R.roots.filter fun z : ℂ => z ≠ 0 := by
    simpa [R, roots] using
      residualPolynomial_selected_roots_add_map_eq_nonzero_roots
        (L := L) (F := F) hF hunit_even
  have hpair_card :
      2 * roots.card = (R.roots.filter fun z : ℂ => z ≠ 0).card := by
    have h := congrArg Multiset.card hroots
    simpa [Nat.two_mul, Multiset.card_add] using h
  have hzero_budget :
      R.rootMultiplicity 0 = 2 * L - R.natDegree := by
    simpa [R] using
      residualPolynomial_rootMultiplicity_zero_eq_budget_sub_natDegree
        (L := L) (F := F) hF hres0
  have hfilter_card :
      (R.roots.filter fun z : ℂ => z ≠ 0).card =
        R.natDegree - R.rootMultiplicity 0 :=
    roots_filter_ne_zero_card R
  have hdegree : R.natDegree ≤ 2 * L := by
    simpa [R] using residualPolynomial_natDegree_le (L := L) (F := F) hF
  have hroot_le_degree : R.rootMultiplicity 0 ≤ R.natDegree := by
    rw [← Polynomial.count_roots R]
    exact (Multiset.count_le_card 0 R.roots).trans
      (le_of_eq (IsAlgClosed.card_roots_eq_natDegree (p := R)))
  have hroots_card_le : roots.card ≤ L := by
    omega
  have hzero : R.rootMultiplicity 0 = L - roots.card := by
    omega
  exact
    PaddedReciprocalConjRootSelection.ofSelectedRoots
      (L := L) (R := R) scale roots hroots_card_le
      (fun z hz => selectedReciprocalConjRoots_nonzero hz)
      (by simpa [R, roots] using hscale)
      hroots hzero

/-- After Wang's selected-root pairing, the residual polynomial is a scalar
multiple of the selected root product's reflected-conjugate norm.  The scalar
is exactly `sourceScalarQuotient`; proving that it is a nonnegative real is the
last scalar step before taking the square root in
[WZYW23, arxiv_v3.tex:2249-2257]. -/
theorem residualPolynomial_eq_sourceScalarQuotient_mul_normPolynomial_selected
    {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L)
    (hres0 : residualPolynomial L F ≠ 0)
    (hunit_even : ∀ z : ℂ, z ≠ 0 → Complex.normSq z = 1 →
      Even ((residualPolynomial L F).roots.count z)) :
    let R : ℂ[X] := residualPolynomial L F
    let roots : Multiset ℂ :=
      selectedReciprocalConjRoots (R.roots.filter fun z : ℂ => z ≠ 0)
    C (sourceScalarQuotient R) * normPolynomial L (sourceRootProduct 1 roots) = R := by
  classical
  intro R roots
  have hroots :
      roots + roots.map reciprocalConj =
        R.roots.filter fun z : ℂ => z ≠ 0 := by
    simpa [R, roots] using
      residualPolynomial_selected_roots_add_map_eq_nonzero_roots
        (L := L) (F := F) hF hunit_even
  have hpair_card :
      2 * roots.card = (R.roots.filter fun z : ℂ => z ≠ 0).card := by
    have h := congrArg Multiset.card hroots
    simpa [Nat.two_mul, Multiset.card_add] using h
  have hzero_budget :
      R.rootMultiplicity 0 = 2 * L - R.natDegree := by
    simpa [R] using
      residualPolynomial_rootMultiplicity_zero_eq_budget_sub_natDegree
        (L := L) (F := F) hF hres0
  have hfilter_card :
      (R.roots.filter fun z : ℂ => z ≠ 0).card =
        R.natDegree - R.rootMultiplicity 0 :=
    roots_filter_ne_zero_card R
  have hdegree : R.natDegree ≤ 2 * L := by
    simpa [R] using residualPolynomial_natDegree_le (L := L) (F := F) hF
  have hroot_le_degree : R.rootMultiplicity 0 ≤ R.natDegree := by
    rw [← Polynomial.count_roots R]
    exact (Multiset.count_le_card 0 R.roots).trans
      (le_of_eq (IsAlgClosed.card_roots_eq_natDegree (p := R)))
  have hroots_card_le : roots.card ≤ L := by
    omega
  have hzero : R.rootMultiplicity 0 = L - roots.card := by
    omega
  let denom : ℂ :=
    (roots.map fun z => -(starRingEnd ℂ z)).prod
  have hdenom_ne : denom ≠ 0 := by
    dsimp [denom, roots, R]
    exact sourceScalarQuotient_denominator_ne_zero (residualPolynomial L F)
  have hq_mul_denom :
      sourceScalarQuotient R * denom = R.leadingCoeff := by
    dsimp [sourceScalarQuotient, denom, roots]
    exact div_mul_cancel₀ R.leadingCoeff hdenom_ne
  have hnorm :
      normPolynomial L (sourceRootProduct 1 roots) =
        X ^ (L - roots.card) *
          sourceRootProduct denom (roots + roots.map reciprocalConj) := by
    have hbase :=
      normPolynomial_sourceRootProduct_budget (L := L) (scale := 1) (roots := roots)
        (fun z hz => selectedReciprocalConjRoots_nonzero hz)
        hroots_card_le
    simpa [denom] using hbase
  calc
    C (sourceScalarQuotient R) * normPolynomial L (sourceRootProduct 1 roots) =
        C (sourceScalarQuotient R) *
          (X ^ (L - roots.card) *
            sourceRootProduct denom (roots + roots.map reciprocalConj)) := by
          rw [hnorm]
    _ = X ^ (L - roots.card) *
          sourceRootProduct (sourceScalarQuotient R * denom)
            (roots + roots.map reciprocalConj) := by
          simp [sourceRootProduct]
          ring
    _ = X ^ R.rootMultiplicity 0 *
          sourceRootProduct R.leadingCoeff
            (R.roots.filter fun z : ℂ => z ≠ 0) := by
          rw [hq_mul_denom, hroots, hzero]
    _ = sourceRootProduct R.leadingCoeff R.roots := by
          rw [sourceRootProduct_roots_zero_nonzero_filter]
    _ = R := (fullRootProductFactorization R).factor_eq

/-- On the unit circle, the residual polynomial evaluates to `1-|F|²`
[WZYW23, arxiv_v3.tex:2260-2274]. -/
theorem lEval_residualPolynomial {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L)
    (x : ℝ) :
    lEval (2 * L) (residualPolynomial L F) x =
      1 - lEval L F x * starRingEnd ℂ (lEval L F x) := by
  rw [residualPolynomial, lEval_sub, lEval_two_mul_X_pow, lEval_normPolynomial hF]

/-- The residual value is the real number `1-‖F(e^{ix})‖²`, under the Laurent
encoding. -/
theorem lEval_residualPolynomial_eq_ofReal {L : ℕ} {F : ℂ[X]}
    (hF : F.natDegree ≤ L) (x : ℝ) :
    lEval (2 * L) (residualPolynomial L F) x =
      ((1 - ‖lEval L F x‖ ^ 2 : ℝ) : ℂ) := by
  rw [lEval_residualPolynomial hF x, QuantumAlg.mul_conj_eq_norm_sq]
  norm_num

/-- A bounded Laurent polynomial has nonnegative residual values on the unit
circle, the entry point for the root-factor construction in
[WZYW23, arxiv_v3.tex:2260-2274]. -/
theorem BoundedComplementProblem.residual_nonnegative {L : ℕ} {F : ℂ[X]}
    (h : BoundedComplementProblem L F) (x : ℝ) :
    0 ≤ (lEval (2 * L) (residualPolynomial L F) x).re := by
  have hsq : ‖lEval L F x‖ ^ 2 ≤ (1 : ℝ) ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg (lEval L F x)]) (h.bounded x)
  rw [lEval_residualPolynomial_eq_ofReal
    (Polynomial.natDegree_le_iff_degree_le.mpr h.degree_A) x]
  change 0 ≤ 1 - ‖lEval L F x‖ ^ 2
  nlinarith

/-- The residual values are real on the unit circle. -/
theorem lEval_residualPolynomial_im {L : ℕ} {F : ℂ[X]}
    (hF : F.natDegree ≤ L) (x : ℝ) :
    (lEval (2 * L) (residualPolynomial L F) x).im = 0 := by
  rw [lEval_residualPolynomial_eq_ofReal hF x]
  exact Complex.ofReal_im _

/-- Conditional scalar-positivity step for Wang's selected-root construction:
if the selected root product is nonzero at one unit-circle point, then the
source scalar quotient is a nonnegative real number.  The remaining global
existence obligation is only to choose such a point outside the finite selected
root set [WZYW23, arxiv_v3.tex:2249-2257]. -/
theorem BoundedComplementProblem.sourceScalarQuotient_real_nonnegative_of_eval_ne_zero
    {L : ℕ} {F : ℂ[X]} (h : BoundedComplementProblem L F)
    (hres0 : residualPolynomial L F ≠ 0)
    (hunit_even : ∀ z : ℂ, z ≠ 0 → Complex.normSq z = 1 →
      Even ((residualPolynomial L F).roots.count z))
    (x : ℝ)
    (hroot_ne :
      lEval L
        (sourceRootProduct 1
          (selectedReciprocalConjRoots
            ((residualPolynomial L F).roots.filter fun z : ℂ => z ≠ 0))) x ≠ 0) :
    (sourceScalarQuotient (residualPolynomial L F)).im = 0 ∧
      0 ≤ (sourceScalarQuotient (residualPolynomial L F)).re := by
  classical
  let R : ℂ[X] := residualPolynomial L F
  let roots : Multiset ℂ :=
    selectedReciprocalConjRoots (R.roots.filter fun z : ℂ => z ≠ 0)
  let S : ℂ[X] := sourceRootProduct 1 roots
  let q : ℂ := sourceScalarQuotient R
  have hF : F.natDegree ≤ L :=
    Polynomial.natDegree_le_iff_degree_le.mpr h.degree_A
  have hroots :
      roots + roots.map reciprocalConj =
        R.roots.filter fun z : ℂ => z ≠ 0 := by
    simpa [R, roots] using
      residualPolynomial_selected_roots_add_map_eq_nonzero_roots
        (L := L) (F := F) hF hunit_even
  have hpair_card :
      2 * roots.card = (R.roots.filter fun z : ℂ => z ≠ 0).card := by
    have hcard := congrArg Multiset.card hroots
    simpa [Nat.two_mul, Multiset.card_add] using hcard
  have hzero_budget :
      R.rootMultiplicity 0 = 2 * L - R.natDegree := by
    simpa [R] using
      residualPolynomial_rootMultiplicity_zero_eq_budget_sub_natDegree
        (L := L) (F := F) hF hres0
  have hfilter_card :
      (R.roots.filter fun z : ℂ => z ≠ 0).card =
        R.natDegree - R.rootMultiplicity 0 :=
    roots_filter_ne_zero_card R
  have hdegree : R.natDegree ≤ 2 * L := by
    simpa [R] using residualPolynomial_natDegree_le (L := L) (F := F) hF
  have hroot_le_degree : R.rootMultiplicity 0 ≤ R.natDegree := by
    rw [← Polynomial.count_roots R]
    exact (Multiset.count_le_card 0 R.roots).trans
      (le_of_eq (IsAlgClosed.card_roots_eq_natDegree (p := R)))
  have hroots_card_le : roots.card ≤ L := by
    omega
  have hS_degree : S.natDegree ≤ L := by
    dsimp [S]
    exact sourceRootProduct_natDegree_le (scale := 1) (roots := roots) hroots_card_le
  have hpoly :
      C q * normPolynomial L S = R := by
    simpa [R, roots, S, q] using
      residualPolynomial_eq_sourceScalarQuotient_mul_normPolynomial_selected
        (L := L) (F := F) hF hres0 hunit_even
  have heval := congrArg (fun P : ℂ[X] => lEval (2 * L) P x) hpoly
  have hs_ne : lEval L S x ≠ 0 := by
    simpa [R, roots, S] using hroot_ne
  have hnorm_ne : ((‖lEval L S x‖ : ℝ) : ℂ) ^ 2 ≠ 0 := by
    norm_num [pow_two, norm_ne_zero_iff.mpr hs_ne]
  have heval_eq :
      lEval (2 * L) R x =
        q * (((‖lEval L S x‖ : ℝ) : ℂ) ^ 2) := by
    rw [← heval]
    rw [lEval_C_mul, lEval_normPolynomial hS_degree]
    rw [mul_conj_eq_norm_sq]
  have hq_eq :
      q = lEval (2 * L) R x / (((‖lEval L S x‖ : ℝ) : ℂ) ^ 2) := by
    rw [heval_eq, mul_div_cancel_right₀ _ hnorm_ne]
  have hR_real :
      (lEval (2 * L) R x).im = 0 := by
    simpa [R] using lEval_residualPolynomial_im (L := L) (F := F) hF x
  have hR_nonneg :
      0 ≤ (lEval (2 * L) R x).re := by
    simpa [R] using BoundedComplementProblem.residual_nonnegative (L := L) (F := F) h x
  let d : ℝ := ‖lEval L S x‖ ^ 2
  have hd_pos : 0 < d := by
    dsimp [d]
    exact sq_pos_of_pos (norm_pos_iff.mpr hs_ne)
  have hdenom_eq :
      (((‖lEval L S x‖ : ℝ) : ℂ) ^ 2) = (d : ℂ) := by
    dsimp [d]
    norm_num [pow_two]
  have hq_eq_real :
      q = lEval (2 * L) R x / (d : ℂ) := by
    rw [hq_eq, hdenom_eq]
  constructor
  · change q.im = 0
    rw [hq_eq_real]
    simp [hR_real]
  · change 0 ≤ q.re
    rw [hq_eq_real]
    rw [Complex.div_ofReal_re]
    exact div_nonneg hR_nonneg (le_of_lt hd_pos)

/-- Unit-circle residual roots of a bounded Laurent target have even
multiplicity.  This is the local sign-change argument in Wang's
Laurent-complement proof: after parametrizing the unit circle by
`z = exp(ix)`, an odd-order zero would force the real nonnegative residual
`1-|F|²` to change sign [WZYW23, arxiv_v3.tex:2241-2257]. -/
theorem BoundedComplementProblem.residual_unitCircle_roots_even
    {L : ℕ} {F : ℂ[X]} (h : BoundedComplementProblem L F)
    (hres0 : residualPolynomial L F ≠ 0) {z : ℂ}
    (_hz0 : z ≠ 0) (hunit : Complex.normSq z = 1) :
    Even ((residualPolynomial L F).roots.count z) := by
  classical
  let R : ℂ[X] := residualPolynomial L F
  have hF : F.natDegree ≤ L :=
    Polynomial.natDegree_le_iff_degree_le.mpr h.degree_A
  by_cases hroot : Polynomial.IsRoot R z
  · rw [Polynomial.count_roots]
    rcases exists_phase_of_normSq_eq_one hunit with ⟨x, hx⟩
    let m : ℕ := R.rootMultiplicity z
    rcases Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd R
        (by simpa [R] using hres0) z with
      ⟨Q, hfactor_poly, hQ_not_dvd⟩
    have hQ_eval_ne : Q.eval z ≠ 0 := by
      intro hQeval
      have hQroot : Polynomial.IsRoot Q z := by
        simpa [Polynomial.IsRoot.def] using hQeval
      exact hQ_not_dvd ((Polynomial.dvd_iff_isRoot).mpr hQroot)
    have hroot_phase :
        R.rootMultiplicity (Complex.exp ((x : ℂ) * Complex.I)) = m := by
      dsimp [m]
      rw [hx]
    let f : ℝ → ℂ := fun t => lEval (2 * L) R t
    let qlocal : ℝ → ℂ := fun t =>
      Complex.exp (-((((2 * L) * t / 2 : ℝ) : ℂ) * Complex.I)) *
        (circleParamSlope x t) ^ m *
        Q.eval (Complex.exp ((t : ℂ) * Complex.I))
    have hnonneg : ∀ᶠ t in nhds x, 0 ≤ (f t).re :=
      Filter.Eventually.of_forall fun t => by
        simpa [f, R] using
          BoundedComplementProblem.residual_nonnegative (L := L) (F := F) h t
    have hreal : ∀ᶠ t in nhds x, (f t).im = 0 :=
      Filter.Eventually.of_forall fun t => by
        simpa [f, R] using
          lEval_residualPolynomial_im (L := L) (F := F) hF t
    have hfactor :
        ∀ᶠ t in nhds x,
          f t = (((t - x) ^ m : ℝ) : ℂ) * qlocal t := by
      apply Filter.Eventually.of_forall
      intro t
      dsimp [f, qlocal]
      rw [lEval]
      rw [hfactor_poly, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      rw [← hx, circleParam_sub_eq x t, mul_pow]
      push_cast
      rw [hroot_phase]
      ring_nf
    have hphase_cont :
        ContinuousAt
          (fun t : ℝ =>
            Complex.exp (-((((2 * L) * t / 2 : ℝ) : ℂ) * Complex.I))) x := by
      have hreal_linear :
          HasDerivAt (fun t : ℝ => (2 * L : ℝ) * t / 2)
            ((2 * L : ℝ) / 2) x :=
        by
          simpa [id, mul_one] using
            ((hasDerivAt_id x).const_mul (2 * L : ℝ)).div_const 2
      have hcomplex_linear :
          HasDerivAt (fun t : ℝ => (((2 * L : ℝ) * t / 2 : ℝ) : ℂ))
            (((2 * L : ℝ) / 2 : ℝ) : ℂ) x :=
        hreal_linear.ofReal_comp
      have harg :
          HasDerivAt
            (fun t : ℝ => -(((((2 * L : ℝ) * t / 2 : ℝ) : ℂ) * Complex.I)))
            (-((((2 * L : ℝ) / 2 : ℝ) : ℂ) * Complex.I)) x :=
        (hcomplex_linear.mul_const Complex.I).neg
      simpa using harg.cexp.continuousAt
    have hQ_cont :
        ContinuousAt
          (fun t : ℝ => Q.eval (Complex.exp ((t : ℂ) * Complex.I))) x := by
      have hcircle_cont :
          ContinuousAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) x :=
        (differentiableAt_circleParam x).continuousAt
      exact (Polynomial.continuousAt (p := Q)).comp hcircle_cont
    have hq_cont : ContinuousAt qlocal x := by
      dsimp [qlocal]
      exact (hphase_cont.mul ((continuousAt_circleParamSlope x).pow m)).mul hQ_cont
    have hq_ne : qlocal x ≠ 0 := by
      dsimp [qlocal]
      rw [hx]
      exact mul_ne_zero
        (mul_ne_zero (Complex.exp_ne_zero _)
          (pow_ne_zero _ (circleParamSlope_self_ne_zero x)))
        hQ_eval_ne
    have hm_even : Even m :=
      even_of_eventually_nonnegative_realvalued_local_complex_pow
        (s := x) (m := m) (f := f) (q := qlocal)
        hnonneg hreal hfactor hq_cont hq_ne
    simpa [m, R]
      using hm_even
  · rw [Polynomial.count_roots, Polynomial.rootMultiplicity_eq_zero hroot]
    exact ⟨0, rfl⟩

/-- Wang's bounded Laurent complement construction supplies a nonnegative real
source scalar quotient.  The proof combines the unit-circle even-multiplicity
argument with a roots-of-unity sampling point outside the selected finite root
set [WZYW23, arxiv_v3.tex:2241-2274]. -/
theorem BoundedComplementProblem.sourceScalarQuotient_real_nonnegative
    {L : ℕ} {F : ℂ[X]} (h : BoundedComplementProblem L F)
    (hres0 : residualPolynomial L F ≠ 0) :
    (sourceScalarQuotient (residualPolynomial L F)).im = 0 ∧
      0 ≤ (sourceScalarQuotient (residualPolynomial L F)).re := by
  classical
  let R : ℂ[X] := residualPolynomial L F
  let roots : Multiset ℂ :=
    selectedReciprocalConjRoots (R.roots.filter fun z : ℂ => z ≠ 0)
  have hF : F.natDegree ≤ L :=
    Polynomial.natDegree_le_iff_degree_le.mpr h.degree_A
  have hunit_even : ∀ z : ℂ, z ≠ 0 → Complex.normSq z = 1 →
      Even ((residualPolynomial L F).roots.count z) := by
    intro z hz0 hunit
    exact BoundedComplementProblem.residual_unitCircle_roots_even h hres0 hz0 hunit
  have hroots :
      roots + roots.map reciprocalConj =
        R.roots.filter fun z : ℂ => z ≠ 0 := by
    simpa [R, roots] using
      residualPolynomial_selected_roots_add_map_eq_nonzero_roots
        (L := L) (F := F) hF hunit_even
  have hpair_card :
      2 * roots.card = (R.roots.filter fun z : ℂ => z ≠ 0).card := by
    have hcard := congrArg Multiset.card hroots
    simpa [Nat.two_mul, Multiset.card_add] using hcard
  have hzero_budget :
      R.rootMultiplicity 0 = 2 * L - R.natDegree := by
    simpa [R] using
      residualPolynomial_rootMultiplicity_zero_eq_budget_sub_natDegree
        (L := L) (F := F) hF hres0
  have hfilter_card :
      (R.roots.filter fun z : ℂ => z ≠ 0).card =
        R.natDegree - R.rootMultiplicity 0 :=
    roots_filter_ne_zero_card R
  have hdegree : R.natDegree ≤ 2 * L := by
    simpa [R] using residualPolynomial_natDegree_le (L := L) (F := F) hF
  have hroot_le_degree : R.rootMultiplicity 0 ≤ R.natDegree := by
    rw [← Polynomial.count_roots R]
    exact (Multiset.count_le_card 0 R.roots).trans
      (le_of_eq (IsAlgClosed.card_roots_eq_natDegree (p := R)))
  have hroots_card_le : roots.card ≤ L := by
    omega
  rcases exists_phase_lEval_sourceRootProduct_ne_zero
      (L := L) (roots := roots) hroots_card_le with ⟨x, hx⟩
  exact
    BoundedComplementProblem.sourceScalarQuotient_real_nonnegative_of_eval_ne_zero
      h hres0 hunit_even x (by simpa [R, roots] using hx)

/-- A complement certificate is exactly the polynomial normalization identity
needed by the YZZYZ/QSP pair condition. -/
theorem ComplementCertificate.polynomial_normalization {L : ℕ} {A : ℂ[X]}
    (h : ComplementCertificate L A) :
    A * (conjP A).reflect L + h.complement * (conjP h.complement).reflect L = X ^ L := by
  simpa [normPolynomial] using h.normalization

/-- Pointwise circle normalization obtained from a complement certificate. -/
theorem ComplementCertificate.circle_normalization {L : ℕ} {A : ℂ[X]}
    (h : ComplementCertificate L A) (hA : A.natDegree ≤ L) (x : ℝ) :
    lEval L A x * starRingEnd ℂ (lEval L A x)
      + lEval L h.complement x * starRingEnd ℂ (lEval L h.complement x) = 1 := by
  have hB : h.complement.natDegree ≤ L :=
    Polynomial.natDegree_le_iff_degree_le.mpr h.degree_complement
  have hnorm := congrArg (fun P : ℂ[X] => lEval (2 * L) P x) h.normalization
  rw [lEval_add, lEval_normPolynomial hA, lEval_normPolynomial hB,
    lEval_two_mul_X_pow] at hnorm
  simpa using hnorm

/-- Package a source square-root factorization of `X^L - |A|^2` as a Laurent
complement certificate. -/
def ComplementCertificate.ofSquareRoot {L : ℕ} {A : ℂ[X]}
    (hroot : SquareRootCertificate L (residualPolynomial L A)) :
    ComplementCertificate L A where
  complement := hroot.root
  degree_complement := hroot.degree_root
  normalization := by
    rw [hroot.factor_eq]
    simp [residualPolynomial]

/-- If `1-|A|²` is identically zero, the zero polynomial is the Laurent
complement.  This is the trivial branch in Wang's Laurent-complement lemma
[WZYW23, arxiv_v3.tex:2271-2273]. -/
def ComplementCertificate.ofResidualEqZero {L : ℕ} {A : ℂ[X]}
    (hres : residualPolynomial L A = 0) :
    ComplementCertificate L A where
  complement := 0
  degree_complement := by
    rw [Polynomial.degree_zero]
    exact bot_le
  normalization := by
    have hnorm : normPolynomial L A = X ^ L := by
      rw [residualPolynomial] at hres
      exact (sub_eq_zero.mp hres).symm
    have hzero : normPolynomial L (0 : ℂ[X]) = 0 := by
      rw [normPolynomial, conjP_zero, Polynomial.reflect_zero, zero_mul]
    rw [hnorm, hzero, add_zero]

/-- A square-root factorization of `1-|A|²` is enough to solve the bounded
complement problem.  The remaining Wang appendix work is exactly to build this
square root from `BoundedComplementProblem` by root classification. -/
theorem hasComplement_ofSquareRoot {L : ℕ} {A : ℂ[X]}
    (hroot : SquareRootCertificate L (residualPolynomial L A)) :
    HasComplement L A :=
  ⟨ComplementCertificate.ofSquareRoot hroot⟩

/-- A Wang root-product square-root certificate solves the Laurent complement
problem.  The remaining nontrivial source work is to build this certificate by
reciprocal-conjugate root pairing [WZYW23, arxiv_v3.tex:2241-2257]. -/
theorem hasComplement_of_sourceSquareRoot {L : ℕ} {A : ℂ[X]}
    (hroot : SourceSquareRootCertificate L (residualPolynomial L A)) :
    HasComplement L A :=
  hasComplement_ofSquareRoot hroot.toSquareRootCertificate

/-- Wang's reciprocal-conjugate root selection is enough to solve the Laurent
complement problem [WZYW23, arxiv_v3.tex:2249-2274]. -/
theorem hasComplement_of_reciprocalConjRootSelection {L : ℕ} {A : ℂ[X]}
    (hroot : ReciprocalConjRootSelection L (residualPolynomial L A)) :
    HasComplement L A :=
  hasComplement_of_sourceSquareRoot hroot.toSourceSquareRootCertificate

/-- A padded reciprocal-conjugate root selection is enough to solve the Laurent
complement problem, including zero-root padding cases [WZYW23,
arxiv_v3.tex:2237-2274]. -/
theorem hasComplement_of_paddedReciprocalConjRootSelection {L : ℕ} {A : ℂ[X]}
    (hroot : PaddedReciprocalConjRootSelection L (residualPolynomial L A)) :
    HasComplement L A :=
  hasComplement_of_sourceSquareRoot hroot.toSourceSquareRootCertificate

/-- Bounded Laurent data has a complement once the two remaining Wang root
classification facts are supplied: unit-circle roots have even multiplicity,
and the source scalar has a square-root choice.  This packages the completed
algebraic part of the Laurent-complement proof [WZYW23,
arxiv_v3.tex:2237-2274]. -/
theorem BoundedComplementProblem.hasComplement_of_unitCircleEven_and_scale
    {L : ℕ} {F : ℂ[X]} (h : BoundedComplementProblem L F)
    (hres0 : residualPolynomial L F ≠ 0)
    (hunit_even : ∀ z : ℂ, z ≠ 0 → Complex.normSq z = 1 →
      Even ((residualPolynomial L F).roots.count z))
    (scale : ℂ)
    (hscale :
      scale * starRingEnd ℂ scale *
        ((selectedReciprocalConjRoots
          ((residualPolynomial L F).roots.filter fun z : ℂ => z ≠ 0)).map
            fun z => -(starRingEnd ℂ z)).prod =
        (residualPolynomial L F).leadingCoeff) :
    HasComplement L F :=
  hasComplement_of_paddedReciprocalConjRootSelection
    (residualPolynomialPaddedSelectionOfUnitCircleEvenAndScale
      (Polynomial.natDegree_le_iff_degree_le.mpr h.degree_A)
      hres0 hunit_even scale hscale)

/-- Bounded Laurent data has a complement once unit-circle root multiplicities
are even and Wang's source scalar quotient is known to be a nonnegative real
number [WZYW23, arxiv_v3.tex:2253-2257]. -/
theorem BoundedComplementProblem.hasComplement_of_unitCircleEven_and_scalarQuotient
    {L : ℕ} {F : ℂ[X]} (h : BoundedComplementProblem L F)
    (hres0 : residualPolynomial L F ≠ 0)
    (hunit_even : ∀ z : ℂ, z ≠ 0 → Complex.normSq z = 1 →
      Even ((residualPolynomial L F).roots.count z))
    (him : (sourceScalarQuotient (residualPolynomial L F)).im = 0)
    (hre : 0 ≤ (sourceScalarQuotient (residualPolynomial L F)).re) :
    HasComplement L F := by
  refine Exists.elim
    (exists_scale_mul_conj_mul_eq_of_div_nonnegative_real
      (c := (residualPolynomial L F).leadingCoeff)
      (k := ((selectedReciprocalConjRoots
        ((residualPolynomial L F).roots.filter fun z : ℂ => z ≠ 0)).map
          (fun z => -(starRingEnd ℂ z))).prod)
      (sourceScalarQuotient_denominator_ne_zero (residualPolynomial L F))
      (by simpa [sourceScalarQuotient] using him)
      (by simpa [sourceScalarQuotient] using hre)) ?_
  intro scale hscale
  exact
    BoundedComplementProblem.hasComplement_of_unitCircleEven_and_scale h
      hres0 hunit_even scale hscale

end Complement.Laurent

namespace Complement.Laurent.Witness

/-- Staged witness name for the square-root route to a Laurent complement. -/
theorem hasComplement_ofSquareRoot {L : ℕ} {A : ℂ[X]}
    (hroot : Complement.Laurent.SquareRootCertificate L
      (Complement.Laurent.residualPolynomial L A)) :
    HasComplement L A :=
  Complement.Laurent.hasComplement_ofSquareRoot hroot

/-- Staged witness name for the source root-product route to a Laurent
complement. -/
theorem hasComplement_of_sourceSquareRoot {L : ℕ} {A : ℂ[X]}
    (hroot : Complement.Laurent.SourceSquareRootCertificate L
      (Complement.Laurent.residualPolynomial L A)) :
    HasComplement L A :=
  Complement.Laurent.hasComplement_of_sourceSquareRoot hroot

/-- Staged witness name for the reciprocal-conjugate root-selection route. -/
theorem hasComplement_of_reciprocalConjRootSelection {L : ℕ} {A : ℂ[X]}
    (hroot : Complement.Laurent.ReciprocalConjRootSelection L
      (Complement.Laurent.residualPolynomial L A)) :
    HasComplement L A :=
  Complement.Laurent.hasComplement_of_reciprocalConjRootSelection hroot

/-- Staged witness name for the padded reciprocal-conjugate root-selection
route. -/
theorem hasComplement_of_paddedReciprocalConjRootSelection {L : ℕ} {A : ℂ[X]}
    (hroot : Complement.Laurent.PaddedReciprocalConjRootSelection L
      (Complement.Laurent.residualPolynomial L A)) :
    HasComplement L A :=
  Complement.Laurent.hasComplement_of_paddedReciprocalConjRootSelection hroot

/-- Staged witness name for the zero-residual Laurent complement branch. -/
theorem hasComplement_of_residual_eq_zero {L : ℕ} {A : ℂ[X]}
    (hres : Complement.Laurent.residualPolynomial L A = 0) :
    HasComplement L A :=
  ⟨Complement.Laurent.ComplementCertificate.ofResidualEqZero hres⟩

end Complement.Laurent.Witness

end

end QuantumAlg
