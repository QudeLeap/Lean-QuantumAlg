/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev
public import QuantumAlg.Util.Polynomial.Complement.Interval.Witness

/-!
# QSP phase-synthesis certificates

This module is the QSP-facing layer of the source-aligned QSVT closeout.  The
polynomial algebra stays in `Util/Polynomial`; this file records the certificate
shape used to pass from the real bounded-polynomial completion theorem of
Gilyen--Su--Low--Wiebe [GSLW19, BlockHam.tex:544-557] to the existing
reflection-QSP completeness theorem.
-/

@[expose] public section

namespace QuantumAlg

open Polynomial Complex

namespace ReflectionQSPPhaseSynthesis

/-- The source-facing hypotheses of the real-polynomial QSP corollary
[GSLW19, BlockHam.tex:544-557]: a real degree-`d` polynomial with matching
parity and `|P(x)| <= 1` on `[-1,1]`. -/
structure RealBoundedMatchingParity (d : ℕ) (PRe : ℝ[X]) where
  degree_le : PRe.natDegree ≤ d
  parity : Complement.Interval.HasRealParity PRe d
  bounded : Complement.Interval.BoundedByOneOnUnitInterval PRe

namespace RealBoundedMatchingParity

/-- The polynomial to which the interval-square theorem is applied in the
real-polynomial QSP corollary [GSLW19, BlockHam.tex:544-557]. -/
noncomputable def squareTarget (PRe : ℝ[X]) : ℝ[X] :=
  1 - PRe ^ 2

/-- The boundedness hypothesis makes `1 - P_re^2` nonnegative on `[-1,1]`,
matching the input condition of [GSLW19, BlockHam.tex:436-438]. -/
theorem squareTarget_nonnegative {d : ℕ} {PRe : ℝ[X]}
    (hP : RealBoundedMatchingParity d PRe) :
    Complement.Interval.NonnegativeOnUnitInterval (squareTarget PRe) := by
  simpa [squareTarget] using
    Complement.Interval.one_sub_sq_nonnegative_of_bounded hP.bounded

/-- Degree input for the interval-square theorem: if `deg(P_re) <= d`, then
`deg(1 - P_re^2) <= 2d` [GSLW19, BlockHam.tex:436-438,544-557]. -/
theorem squareTarget_natDegree_le {d : ℕ} {PRe : ℝ[X]}
    (hP : RealBoundedMatchingParity d PRe) :
    (squareTarget PRe).natDegree ≤ 2 * d := by
  unfold squareTarget
  have hone : (1 : ℝ[X]).natDegree ≤ 2 * d := by simp
  have hsq : (PRe ^ 2).natDegree ≤ 2 * d :=
    Polynomial.natDegree_pow_le_of_le 2 hP.degree_le
  simpa using
    (Polynomial.natDegree_sub_le_of_le
      (p := (1 : ℝ[X])) (q := PRe ^ 2) hone hsq)

/-- Parity input for the interval-square theorem: `1 - P_re^2` is even
whenever `P_re` has a fixed parity [GSLW19, BlockHam.tex:436-438,544-557]. -/
theorem squareTarget_even {d : ℕ} {PRe : ℝ[X]}
    (hP : RealBoundedMatchingParity d PRe) :
    Complement.Interval.HasRealParity (squareTarget PRe) 0 := by
  unfold squareTarget
  exact (Complement.Interval.hasRealParity_one (by rfl)).sub
    hP.parity.square_even

/-- Package the real-polynomial QSP hypotheses as the exact input of the
interval-square decomposition theorem [GSLW19, BlockHam.tex:436-438,544-557]. -/
theorem squareTarget_sourceHypotheses {d : ℕ} {PRe : ℝ[X]}
    (hP : RealBoundedMatchingParity d PRe) :
    Complement.Interval.SourceHypotheses (squareTarget PRe) d where
  degree_le := squareTarget_natDegree_le hP
  even := squareTarget_even hP
  nonnegative := squareTarget_nonnegative hP

end RealBoundedMatchingParity

/-- Complex-polynomial matching-parity and interval-boundedness hypotheses.

This is deliberately only an interval-bounded record.  It is not a phase
existence certificate: `thm:achievablePorQ` has additional source-side
conditions outside `[-1,1]` and on the imaginary axis [GSLW19,
BlockHam.tex:392-405]. -/
structure ComplexIntervalBoundedMatchingParity (d : ℕ) (P : ℂ[X]) where
  degree_le : P.natDegree ≤ d
  parity : HasParity P d
  bounded :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1

/-- Real-polynomial parity is preserved by the coefficient embedding
`ℝ[X] -> ℂ[X]`. -/
theorem hasParity_realPolynomialToComplex {PRe : ℝ[X]} {p : ℕ}
    (hP : Complement.Interval.HasRealParity PRe p) :
    HasParity (realPolynomialToComplex PRe) p := by
  intro k hk
  rw [realPolynomialToComplex, Polynomial.coeff_map] at hk
  exact hP k (fun hzero => hk (by simp [hzero]))

/-- Degree bounds for real polynomials transfer to the complex coefficient
embedding used by the QSP completion. -/
theorem degree_realPolynomialToComplex_le {PRe : ℝ[X]} {d : ℕ}
    (hdeg : PRe.natDegree ≤ d) :
    (realPolynomialToComplex PRe).degree ≤ d := by
  rw [realPolynomialToComplex_degree]
  exact Polynomial.degree_le_of_natDegree_le hdeg

/-- The embedded real polynomial has the requested real part on real inputs. -/
theorem realPolynomialToComplex_real_part_matches (PRe : ℝ[X]) :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      ((realPolynomialToComplex PRe).eval (x : ℂ)).re = PRe.eval x := by
  intro x _hx
  rw [realPolynomialToComplex_eval_ofReal]
  simp

/-- The coefficientwise even part has real parity zero. -/
theorem hasRealParity_realPolynomialEvenPart (P : ℝ[X]) :
    Complement.Interval.HasRealParity (realPolynomialEvenPart P) 0 := by
  intro n hn
  rw [realPolynomialEvenPart_coeff] at hn
  by_cases h : n % 2 = 0
  · simp [h]
  · simp [h] at hn

/-- The coefficientwise odd part has real parity one. -/
theorem hasRealParity_realPolynomialOddPart (P : ℝ[X]) :
    Complement.Interval.HasRealParity (realPolynomialOddPart P) 1 := by
  intro n hn
  rw [realPolynomialOddPart_coeff] at hn
  by_cases h : n % 2 = 1
  · simp [h]
  · simp [h] at hn

/-- Multiplying a real polynomial by a scalar preserves its coefficient parity. -/
theorem hasRealParity_smul (c : ℝ) {P : ℝ[X]} {d : ℕ}
    (hP : Complement.Interval.HasRealParity P d) :
    Complement.Interval.HasRealParity (c • P) d := by
  intro n hn
  apply hP n
  intro hcoeff
  rw [Polynomial.coeff_smul, hcoeff] at hn
  simp at hn

/-- If `|P(x)| <= 1/2` on the unit interval, then `2 * even(P)` is bounded by
one there.  This is the normalized even branch of the arbitrary-parity split
in `thm:arbParity` [GSLW19, BlockHam.tex:1936-1951]. -/
theorem two_smul_realPolynomialEvenPart_boundedByOne_of_boundedByHalf
    (P : ℝ[X])
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |P.eval x| ≤ (1 / 2 : ℝ)) :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      |(((2 : ℝ) • realPolynomialEvenPart P).eval x)| ≤ 1 := by
  intro x hx
  have hxneg : -x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hsum :
      |P.eval x + P.eval (-x)| ≤ 1 := by
    calc
      |P.eval x + P.eval (-x)| ≤ |P.eval x| + |P.eval (-x)| :=
        abs_add_le _ _
      _ ≤ (1 / 2 : ℝ) + (1 / 2 : ℝ) :=
        add_le_add (hbound x hx) (hbound (-x) hxneg)
      _ = 1 := by norm_num
  rw [Polynomial.eval_smul, realPolynomialEvenPart_eval]
  have heq :
      (2 : ℝ) * ((P.eval x + P.eval (-x)) / 2) =
        P.eval x + P.eval (-x) := by ring
  simpa [heq] using hsum

/-- If `|P(x)| <= 1/2` on the unit interval, then `2 * odd(P)` is bounded by
one there.  This is the normalized odd branch of the arbitrary-parity split in
`thm:arbParity` [GSLW19, BlockHam.tex:1936-1951]. -/
theorem two_smul_realPolynomialOddPart_boundedByOne_of_boundedByHalf
    (P : ℝ[X])
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |P.eval x| ≤ (1 / 2 : ℝ)) :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      |(((2 : ℝ) • realPolynomialOddPart P).eval x)| ≤ 1 := by
  intro x hx
  have hxneg : -x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hdiff :
      |P.eval x - P.eval (-x)| ≤ 1 := by
    calc
      |P.eval x - P.eval (-x)| = |P.eval x + -P.eval (-x)| := by ring_nf
      _ ≤ |P.eval x| + |-P.eval (-x)| := abs_add_le _ _
      _ = |P.eval x| + |P.eval (-x)| := by simp
      _ ≤ (1 / 2 : ℝ) + (1 / 2 : ℝ) :=
        add_le_add (hbound x hx) (hbound (-x) hxneg)
      _ = 1 := by norm_num
  rw [Polynomial.eval_smul, realPolynomialOddPart_eval]
  have heq :
      (2 : ℝ) * ((P.eval x - P.eval (-x)) / 2) =
        P.eval x - P.eval (-x) := by ring
  simpa [heq] using hdiff

/-- Real part of a norm-bounded complex polynomial, restricted to its even
coefficient part, supplies the real matching-parity QSP hypotheses. -/
theorem realBoundedMatchingParity_realEvenPart_of_normSq_le {d : ℕ} (P : ℂ[X])
    (hdegree : P.natDegree ≤ d) (hd : d % 2 = 0)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    RealBoundedMatchingParity d
      (realPolynomialEvenPart (complexPolynomialRealPart P)) where
  degree_le :=
    (realPolynomialEvenPart_natDegree_le (complexPolynomialRealPart P)).trans
      ((complexPolynomialRealPart_natDegree_le P).trans hdegree)
  parity :=
    (hasRealParity_realPolynomialEvenPart (complexPolynomialRealPart P)).congr hd.symm
  bounded :=
    realPolynomialEvenPart_boundedByOne_of_boundedByOne
      (complexPolynomialRealPart P)
      (complexPolynomialRealPart_boundedByOne_of_normSq_le P hbound)

/-- Real part of a norm-bounded complex polynomial, restricted to its odd
coefficient part, supplies the real matching-parity QSP hypotheses. -/
theorem realBoundedMatchingParity_realOddPart_of_normSq_le {d : ℕ} (P : ℂ[X])
    (hdegree : P.natDegree ≤ d) (hd : d % 2 = 1)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    RealBoundedMatchingParity d
      (realPolynomialOddPart (complexPolynomialRealPart P)) where
  degree_le :=
    (realPolynomialOddPart_natDegree_le (complexPolynomialRealPart P)).trans
      ((complexPolynomialRealPart_natDegree_le P).trans hdegree)
  parity :=
    (hasRealParity_realPolynomialOddPart (complexPolynomialRealPart P)).congr hd.symm
  bounded :=
    realPolynomialOddPart_boundedByOne_of_boundedByOne
      (complexPolynomialRealPart P)
      (complexPolynomialRealPart_boundedByOne_of_normSq_le P hbound)

/-- Imaginary part of a norm-bounded complex polynomial, restricted to its even
coefficient part, supplies the real matching-parity QSP hypotheses. -/
theorem realBoundedMatchingParity_imagEvenPart_of_normSq_le {d : ℕ} (P : ℂ[X])
    (hdegree : P.natDegree ≤ d) (hd : d % 2 = 0)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    RealBoundedMatchingParity d
      (realPolynomialEvenPart (complexPolynomialImagPart P)) where
  degree_le :=
    (realPolynomialEvenPart_natDegree_le (complexPolynomialImagPart P)).trans
      ((complexPolynomialImagPart_natDegree_le P).trans hdegree)
  parity :=
    (hasRealParity_realPolynomialEvenPart (complexPolynomialImagPart P)).congr hd.symm
  bounded :=
    realPolynomialEvenPart_boundedByOne_of_boundedByOne
      (complexPolynomialImagPart P)
      (complexPolynomialImagPart_boundedByOne_of_normSq_le P hbound)

/-- Imaginary part of a norm-bounded complex polynomial, restricted to its odd
coefficient part, supplies the real matching-parity QSP hypotheses. -/
theorem realBoundedMatchingParity_imagOddPart_of_normSq_le {d : ℕ} (P : ℂ[X])
    (hdegree : P.natDegree ≤ d) (hd : d % 2 = 1)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    RealBoundedMatchingParity d
      (realPolynomialOddPart (complexPolynomialImagPart P)) where
  degree_le :=
    (realPolynomialOddPart_natDegree_le (complexPolynomialImagPart P)).trans
      ((complexPolynomialImagPart_natDegree_le P).trans hdegree)
  parity :=
    (hasRealParity_realPolynomialOddPart (complexPolynomialImagPart P)).congr hd.symm
  bounded :=
    realPolynomialOddPart_boundedByOne_of_boundedByOne
      (complexPolynomialImagPart P)
      (complexPolynomialImagPart_boundedByOne_of_normSq_le P hbound)

/-- If the ambient degree bound is odd, the even real part drops to degree
`L-1`, which matches the even-parity branch used in `thm:arbParity`
[GSLW19, BlockHam.tex:1936-1951]. -/
theorem realBoundedMatchingParity_realEvenPart_of_normSq_le_pred_of_odd_bound
    {L : ℕ} (P : ℂ[X]) (hdegree : P.natDegree ≤ L) (hLodd : L % 2 = 1)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    RealBoundedMatchingParity (L - 1)
      (realPolynomialEvenPart (complexPolynomialRealPart P)) where
  degree_le :=
    realPolynomialEvenPart_natDegree_le_pred_of_odd_bound
      (complexPolynomialRealPart P)
      ((complexPolynomialRealPart_natDegree_le P).trans hdegree) hLodd
  parity := by
    have hmod : (L - 1) % 2 = 0 := by omega
    exact (hasRealParity_realPolynomialEvenPart (complexPolynomialRealPart P)).congr hmod.symm
  bounded :=
    realPolynomialEvenPart_boundedByOne_of_boundedByOne
      (complexPolynomialRealPart P)
      (complexPolynomialRealPart_boundedByOne_of_normSq_le P hbound)

/-- If the ambient degree bound is odd, the even imaginary part drops to degree
`L-1`, matching the even-parity branch used in the complex-polynomial note
after `thm:arbParity` [GSLW19, BlockHam.tex:1952]. -/
theorem realBoundedMatchingParity_imagEvenPart_of_normSq_le_pred_of_odd_bound
    {L : ℕ} (P : ℂ[X]) (hdegree : P.natDegree ≤ L) (hLodd : L % 2 = 1)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    RealBoundedMatchingParity (L - 1)
      (realPolynomialEvenPart (complexPolynomialImagPart P)) where
  degree_le :=
    realPolynomialEvenPart_natDegree_le_pred_of_odd_bound
      (complexPolynomialImagPart P)
      ((complexPolynomialImagPart_natDegree_le P).trans hdegree) hLodd
  parity := by
    have hmod : (L - 1) % 2 = 0 := by omega
    exact (hasRealParity_realPolynomialEvenPart (complexPolynomialImagPart P)).congr hmod.symm
  bounded :=
    realPolynomialEvenPart_boundedByOne_of_boundedByOne
      (complexPolynomialImagPart P)
      (complexPolynomialImagPart_boundedByOne_of_normSq_le P hbound)

/-- If the ambient degree bound is positive and even, the odd real part drops
to degree `L-1`, which matches the odd-parity branch used in `thm:arbParity`
[GSLW19, BlockHam.tex:1936-1951]. -/
theorem realBoundedMatchingParity_realOddPart_of_normSq_le_pred_of_even_bound
    {L : ℕ} (P : ℂ[X]) (hdegree : P.natDegree ≤ L) (hLpos : 0 < L)
    (hLeven : L % 2 = 0)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    RealBoundedMatchingParity (L - 1)
      (realPolynomialOddPart (complexPolynomialRealPart P)) where
  degree_le :=
    realPolynomialOddPart_natDegree_le_pred_of_even_bound
      (complexPolynomialRealPart P)
      ((complexPolynomialRealPart_natDegree_le P).trans hdegree) hLeven
  parity := by
    have hmod : (L - 1) % 2 = 1 := by omega
    exact (hasRealParity_realPolynomialOddPart (complexPolynomialRealPart P)).congr hmod.symm
  bounded :=
    realPolynomialOddPart_boundedByOne_of_boundedByOne
      (complexPolynomialRealPart P)
      (complexPolynomialRealPart_boundedByOne_of_normSq_le P hbound)

/-- If the ambient degree bound is positive and even, the odd imaginary part
drops to degree `L-1`, matching the odd-parity branch used in the
complex-polynomial note after `thm:arbParity` [GSLW19, BlockHam.tex:1952]. -/
theorem realBoundedMatchingParity_imagOddPart_of_normSq_le_pred_of_even_bound
    {L : ℕ} (P : ℂ[X]) (hdegree : P.natDegree ≤ L) (hLpos : 0 < L)
    (hLeven : L % 2 = 0)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    RealBoundedMatchingParity (L - 1)
      (realPolynomialOddPart (complexPolynomialImagPart P)) where
  degree_le :=
    realPolynomialOddPart_natDegree_le_pred_of_even_bound
      (complexPolynomialImagPart P)
      ((complexPolynomialImagPart_natDegree_le P).trans hdegree) hLeven
  parity := by
    have hmod : (L - 1) % 2 = 1 := by omega
    exact (hasRealParity_realPolynomialOddPart (complexPolynomialImagPart P)).congr hmod.symm
  bounded :=
    realPolynomialOddPart_boundedByOne_of_boundedByOne
      (complexPolynomialImagPart P)
      (complexPolynomialImagPart_boundedByOne_of_normSq_le P hbound)

/-- Degree used for the even branch in arbitrary-parity reductions. If the
ambient degree has odd parity, the even branch has degree at most `L-1`. -/
def evenBranchDegree (L : ℕ) : ℕ :=
  if L % 2 = 0 then L else L - 1

/-- Degree used for the odd branch in arbitrary-parity reductions. For
`L = 0` the odd branch is handled separately as the zero component. -/
def oddBranchDegree (L : ℕ) : ℕ :=
  if L % 2 = 1 then L else L - 1

theorem evenBranchDegree_le (L : ℕ) : evenBranchDegree L ≤ L := by
  unfold evenBranchDegree
  split <;> omega

theorem oddBranchDegree_le (L : ℕ) : oddBranchDegree L ≤ L := by
  unfold oddBranchDegree
  split <;> omega

theorem evenBranchDegree_mod_two (L : ℕ) : evenBranchDegree L % 2 = 0 := by
  unfold evenBranchDegree
  split
  · assumption
  · omega

theorem oddBranchDegree_mod_two {L : ℕ} (hLpos : 0 < L) :
    oddBranchDegree L % 2 = 1 := by
  unfold oddBranchDegree
  split
  · assumption
  · omega

/-- Uniform constructor for the even real branch in the arbitrary-parity split. -/
theorem realBoundedMatchingParity_realEvenPart_branch_of_normSq_le {L : ℕ}
    (P : ℂ[X]) (hdegree : P.natDegree ≤ L)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    RealBoundedMatchingParity (evenBranchDegree L)
      (realPolynomialEvenPart (complexPolynomialRealPart P)) := by
  unfold evenBranchDegree
  by_cases hLeven : L % 2 = 0
  · simpa [hLeven] using
      realBoundedMatchingParity_realEvenPart_of_normSq_le
        (d := L) P hdegree hLeven hbound
  · have hLodd : L % 2 = 1 := by omega
    simpa [hLeven] using
      realBoundedMatchingParity_realEvenPart_of_normSq_le_pred_of_odd_bound
        P hdegree hLodd hbound

/-- Uniform constructor for the even imaginary branch in the arbitrary-parity
complex split. -/
theorem realBoundedMatchingParity_imagEvenPart_branch_of_normSq_le {L : ℕ}
    (P : ℂ[X]) (hdegree : P.natDegree ≤ L)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    RealBoundedMatchingParity (evenBranchDegree L)
      (realPolynomialEvenPart (complexPolynomialImagPart P)) := by
  unfold evenBranchDegree
  by_cases hLeven : L % 2 = 0
  · simpa [hLeven] using
      realBoundedMatchingParity_imagEvenPart_of_normSq_le
        (d := L) P hdegree hLeven hbound
  · have hLodd : L % 2 = 1 := by omega
    simpa [hLeven] using
      realBoundedMatchingParity_imagEvenPart_of_normSq_le_pred_of_odd_bound
        P hdegree hLodd hbound

/-- Uniform constructor for the odd real branch in the arbitrary-parity split,
away from the constant-polynomial edge case. -/
theorem realBoundedMatchingParity_realOddPart_branch_of_normSq_le {L : ℕ}
    (P : ℂ[X]) (hdegree : P.natDegree ≤ L) (hLpos : 0 < L)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    RealBoundedMatchingParity (oddBranchDegree L)
      (realPolynomialOddPart (complexPolynomialRealPart P)) := by
  unfold oddBranchDegree
  by_cases hLodd : L % 2 = 1
  · simpa [hLodd] using
      realBoundedMatchingParity_realOddPart_of_normSq_le
        (d := L) P hdegree hLodd hbound
  · have hLeven : L % 2 = 0 := by omega
    simpa [hLodd] using
      realBoundedMatchingParity_realOddPart_of_normSq_le_pred_of_even_bound
        P hdegree hLpos hLeven hbound

/-- Uniform constructor for the odd imaginary branch in the arbitrary-parity
complex split, away from the constant-polynomial edge case. -/
theorem realBoundedMatchingParity_imagOddPart_branch_of_normSq_le {L : ℕ}
    (P : ℂ[X]) (hdegree : P.natDegree ≤ L) (hLpos : 0 < L)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    RealBoundedMatchingParity (oddBranchDegree L)
      (realPolynomialOddPart (complexPolynomialImagPart P)) := by
  unfold oddBranchDegree
  by_cases hLodd : L % 2 = 1
  · simpa [hLodd] using
      realBoundedMatchingParity_imagOddPart_of_normSq_le
        (d := L) P hdegree hLodd hbound
  · have hLeven : L % 2 = 0 := by omega
    simpa [hLodd] using
      realBoundedMatchingParity_imagOddPart_of_normSq_le_pred_of_even_bound
        P hdegree hLpos hLeven hbound

/-- Uniform constructor for the odd real branch, including the constant
ambient-degree edge case where the odd branch is the zero polynomial. -/
theorem realBoundedMatchingParity_realOddPart_branch_of_normSq_le_including_constant {L : ℕ}
    (P : ℂ[X]) (hdegree : P.natDegree ≤ L)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    RealBoundedMatchingParity (oddBranchDegree L)
      (realPolynomialOddPart (complexPolynomialRealPart P)) := by
  by_cases hLpos : 0 < L
  · exact realBoundedMatchingParity_realOddPart_branch_of_normSq_le P hdegree hLpos hbound
  · have hL0 : L = 0 := by omega
    have hPdeg0 : P.natDegree = 0 := by
      have hle0 : P.natDegree ≤ 0 := by
        simpa [hL0] using hdegree
      exact Nat.eq_zero_of_le_zero hle0
    have hReDeg0 : (complexPolynomialRealPart P).natDegree = 0 := by
      have hle := complexPolynomialRealPart_natDegree_le P
      omega
    have hzero :
        realPolynomialOddPart (complexPolynomialRealPart P) = 0 :=
      realPolynomialOddPart_eq_zero_of_natDegree_eq_zero
        (complexPolynomialRealPart P) hReDeg0
    refine {
      degree_le := ?_,
      parity := ?_,
      bounded := ?_
    }
    · simp [hzero]
    · simpa [hzero] using
        Complement.Interval.hasRealParity_zero (oddBranchDegree L)
    · intro x hx
      simp [hzero]

/-- Uniform constructor for the odd imaginary branch, including the constant
ambient-degree edge case where the odd branch is the zero polynomial. -/
theorem realBoundedMatchingParity_imagOddPart_branch_of_normSq_le_including_constant {L : ℕ}
    (P : ℂ[X]) (hdegree : P.natDegree ≤ L)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    RealBoundedMatchingParity (oddBranchDegree L)
      (realPolynomialOddPart (complexPolynomialImagPart P)) := by
  by_cases hLpos : 0 < L
  · exact realBoundedMatchingParity_imagOddPart_branch_of_normSq_le P hdegree hLpos hbound
  · have hL0 : L = 0 := by omega
    have hPdeg0 : P.natDegree = 0 := by
      have hle0 : P.natDegree ≤ 0 := by
        simpa [hL0] using hdegree
      exact Nat.eq_zero_of_le_zero hle0
    have hImDeg0 : (complexPolynomialImagPart P).natDegree = 0 := by
      have hle := complexPolynomialImagPart_natDegree_le P
      omega
    have hzero :
        realPolynomialOddPart (complexPolynomialImagPart P) = 0 :=
      realPolynomialOddPart_eq_zero_of_natDegree_eq_zero
        (complexPolynomialImagPart P) hImDeg0
    refine {
      degree_le := ?_,
      parity := ?_,
      bounded := ?_
    }
    · simp [hzero]
    · simpa [hzero] using
        Complement.Interval.hasRealParity_zero (oddBranchDegree L)
    · intro x hx
      simp [hzero]

/-- The complex even branch of a norm-bounded polynomial supplies complex
matching-parity hypotheses. -/
theorem complexIntervalBoundedMatchingParity_evenPart_of_normSq_le {d : ℕ} (P : ℂ[X])
    (hdegree : P.natDegree ≤ d) (hd : d % 2 = 0)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ComplexIntervalBoundedMatchingParity d (complexPolynomialEvenPart P) where
  degree_le := (complexPolynomialEvenPart_natDegree_le P).trans hdegree
  parity := (complexPolynomialEvenPart_hasParity P).congr hd.symm
  bounded := complexPolynomialEvenPart_normSq_le_of_normSq_le P hbound

/-- The complex odd branch of a norm-bounded polynomial supplies complex
matching-parity hypotheses. -/
theorem complexIntervalBoundedMatchingParity_oddPart_of_normSq_le {d : ℕ} (P : ℂ[X])
    (hdegree : P.natDegree ≤ d) (hd : d % 2 = 1)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ComplexIntervalBoundedMatchingParity d (complexPolynomialOddPart P) where
  degree_le := (complexPolynomialOddPart_natDegree_le P).trans hdegree
  parity := (complexPolynomialOddPart_hasParity P).congr hd.symm
  bounded := complexPolynomialOddPart_normSq_le_of_normSq_le P hbound

/-- If the ambient degree bound is odd, the complex even branch drops to
degree `L - 1`. -/
theorem complexIntervalBoundedMatchingParity_evenPart_of_normSq_le_pred_of_odd_bound
    {L : ℕ} (P : ℂ[X]) (hdegree : P.natDegree ≤ L) (hLodd : L % 2 = 1)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ComplexIntervalBoundedMatchingParity (L - 1) (complexPolynomialEvenPart P) where
  degree_le := complexPolynomialEvenPart_natDegree_le_pred_of_odd_bound P hdegree hLodd
  parity := by
    have hmod : (L - 1) % 2 = 0 := by omega
    exact (complexPolynomialEvenPart_hasParity P).congr hmod.symm
  bounded := complexPolynomialEvenPart_normSq_le_of_normSq_le P hbound

/-- If the ambient degree bound is positive and even, the complex odd branch
drops to degree `L - 1`. -/
theorem complexIntervalBoundedMatchingParity_oddPart_of_normSq_le_pred_of_even_bound
    {L : ℕ} (P : ℂ[X]) (hdegree : P.natDegree ≤ L) (hLpos : 0 < L)
    (hLeven : L % 2 = 0)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ComplexIntervalBoundedMatchingParity (L - 1) (complexPolynomialOddPart P) where
  degree_le := complexPolynomialOddPart_natDegree_le_pred_of_even_bound P hdegree hLeven
  parity := by
    have hmod : (L - 1) % 2 = 1 := by omega
    exact (complexPolynomialOddPart_hasParity P).congr hmod.symm
  bounded := complexPolynomialOddPart_normSq_le_of_normSq_le P hbound

/-- Uniform constructor for the complex even branch in the arbitrary-parity
split. -/
theorem complexIntervalBoundedMatchingParity_evenPart_branch_of_normSq_le {L : ℕ}
    (P : ℂ[X]) (hdegree : P.natDegree ≤ L)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ComplexIntervalBoundedMatchingParity (evenBranchDegree L) (complexPolynomialEvenPart P) := by
  unfold evenBranchDegree
  by_cases hLeven : L % 2 = 0
  · simpa [hLeven] using
      complexIntervalBoundedMatchingParity_evenPart_of_normSq_le
        (d := L) P hdegree hLeven hbound
  · have hLodd : L % 2 = 1 := by omega
    simpa [hLeven] using
      complexIntervalBoundedMatchingParity_evenPart_of_normSq_le_pred_of_odd_bound
        P hdegree hLodd hbound

/-- Uniform constructor for the complex odd branch, including the
constant-polynomial edge case where the odd branch is zero. -/
theorem complexIntervalBoundedMatchingParity_oddPart_branch_of_normSq_le {L : ℕ}
    (P : ℂ[X]) (hdegree : P.natDegree ≤ L)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ComplexIntervalBoundedMatchingParity (oddBranchDegree L) (complexPolynomialOddPart P) := by
  by_cases hLpos : 0 < L
  · unfold oddBranchDegree
    by_cases hLodd : L % 2 = 1
    · simpa [hLodd] using
        complexIntervalBoundedMatchingParity_oddPart_of_normSq_le
          (d := L) P hdegree hLodd hbound
    · have hLeven : L % 2 = 0 := by omega
      simpa [hLodd] using
        complexIntervalBoundedMatchingParity_oddPart_of_normSq_le_pred_of_even_bound
          P hdegree hLpos hLeven hbound
  · have hL0 : L = 0 := by omega
    have hPdeg0 : P.natDegree = 0 := by
      have hle0 : P.natDegree ≤ 0 := by
        simpa [hL0] using hdegree
      exact Nat.eq_zero_of_le_zero hle0
    have hzero : complexPolynomialOddPart P = 0 :=
      complexPolynomialOddPart_eq_zero_of_natDegree_eq_zero P hPdeg0
    refine {
      degree_le := ?_,
      parity := ?_,
      bounded := ?_
    }
    · simp [hzero]
    · simpa [hzero] using hasParity_zero (oddBranchDegree L)
    · intro x hx
      simp [hzero, Complex.normSq]

/-- The normalized even branch `2 * even(P)` supplies the real matching-parity
QSP hypotheses in the real arbitrary-parity reduction of `thm:arbParity`
[GSLW19, BlockHam.tex:1936-1951]. -/
theorem realBoundedMatchingParity_twoEvenPart_branch_of_boundedByHalf {L : ℕ}
    (P : ℝ[X]) (hdegree : P.natDegree ≤ L)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |P.eval x| ≤ (1 / 2 : ℝ)) :
    RealBoundedMatchingParity (evenBranchDegree L)
      ((2 : ℝ) • realPolynomialEvenPart P) where
  degree_le := by
    unfold evenBranchDegree
    by_cases hLeven : L % 2 = 0
    · simpa [hLeven] using
        (Polynomial.natDegree_smul_le (2 : ℝ) (realPolynomialEvenPart P)).trans
          ((realPolynomialEvenPart_natDegree_le P).trans hdegree)
    · have hLodd : L % 2 = 1 := by omega
      simpa [hLeven] using
        (Polynomial.natDegree_smul_le (2 : ℝ) (realPolynomialEvenPart P)).trans
          (realPolynomialEvenPart_natDegree_le_pred_of_odd_bound P hdegree hLodd)
  parity := by
    exact hasRealParity_smul (2 : ℝ)
      ((hasRealParity_realPolynomialEvenPart P).congr
        (evenBranchDegree_mod_two L).symm)
  bounded :=
    two_smul_realPolynomialEvenPart_boundedByOne_of_boundedByHalf P hbound

/-- The normalized odd branch `2 * odd(P)` supplies the real matching-parity
QSP hypotheses in the real arbitrary-parity reduction of `thm:arbParity`, away
from the constant-polynomial edge case [GSLW19, BlockHam.tex:1936-1951]. -/
theorem realBoundedMatchingParity_twoOddPart_branch_of_boundedByHalf {L : ℕ}
    (P : ℝ[X]) (hdegree : P.natDegree ≤ L) (hLpos : 0 < L)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |P.eval x| ≤ (1 / 2 : ℝ)) :
    RealBoundedMatchingParity (oddBranchDegree L)
      ((2 : ℝ) • realPolynomialOddPart P) where
  degree_le := by
    unfold oddBranchDegree
    by_cases hLodd : L % 2 = 1
    · simpa [hLodd] using
        (Polynomial.natDegree_smul_le (2 : ℝ) (realPolynomialOddPart P)).trans
          ((realPolynomialOddPart_natDegree_le P).trans hdegree)
    · have hLeven : L % 2 = 0 := by omega
      simpa [hLodd] using
        (Polynomial.natDegree_smul_le (2 : ℝ) (realPolynomialOddPart P)).trans
          (realPolynomialOddPart_natDegree_le_pred_of_even_bound P hdegree hLeven)
  parity := by
    exact hasRealParity_smul (2 : ℝ)
      ((hasRealParity_realPolynomialOddPart P).congr
        (oddBranchDegree_mod_two hLpos).symm)
  bounded :=
    two_smul_realPolynomialOddPart_boundedByOne_of_boundedByHalf P hbound

/-- The normalized odd branch, including the constant edge case where the odd
branch is zero. -/
theorem realBoundedMatchingParity_twoOddPart_branch_of_boundedByHalf_including_constant
    {L : ℕ} (P : ℝ[X]) (hdegree : P.natDegree ≤ L)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |P.eval x| ≤ (1 / 2 : ℝ)) :
    RealBoundedMatchingParity (oddBranchDegree L)
      ((2 : ℝ) • realPolynomialOddPart P) := by
  by_cases hLpos : 0 < L
  · exact realBoundedMatchingParity_twoOddPart_branch_of_boundedByHalf
      P hdegree hLpos hbound
  · have hL0 : L = 0 := by omega
    have hPdeg0 : P.natDegree = 0 := by
      have hle0 : P.natDegree ≤ 0 := by
        simpa [hL0] using hdegree
      exact Nat.eq_zero_of_le_zero hle0
    have hzero : realPolynomialOddPart P = 0 :=
      realPolynomialOddPart_eq_zero_of_natDegree_eq_zero P hPdeg0
    refine {
      degree_le := ?_,
      parity := ?_,
      bounded := ?_
    }
    · simp [hzero]
    · simpa [hzero] using
        Complement.Interval.hasRealParity_zero (oddBranchDegree L)
    · intro x hx
      simp [hzero]

/-- The interval-square data used in [GSLW19, BlockHam.tex:436-480] and then
in the real-polynomial corollary [GSLW19, BlockHam.tex:544-557].  For a
degree-`d` matching-parity polynomial `PRe`, the source proves a certificate
for `1 - PRe^2` with the degree/parity bounds needed to form the complementary
QSP polynomial. -/
structure IntervalSquareCompletionData (d : ℕ) (PRe : ℝ[X]) where
  hypotheses : RealBoundedMatchingParity d PRe
  /-- Degree/parity interval-square certificate for `1 - PRe^2`. -/
  squareCertificate :
    Complement.Interval.DegreeParityCertificate (1 - PRe ^ 2) d

/-- Forget degree/parity bounds when only pointwise normalization is needed. -/
noncomputable def IntervalSquareCompletionData.toIntervalCertificate {d : ℕ} {PRe : ℝ[X]}
    (h : IntervalSquareCompletionData d PRe) :
    Complement.Interval.Certificate (1 - PRe ^ 2) :=
  h.squareCertificate.toCertificate

/-- The interval-square data gives the pointwise normalization used to build
the complex QSP completion [GSLW19, BlockHam.tex:475-480,544-557]. -/
theorem IntervalSquareCompletionData.normalization_on_interval {d : ℕ} {PRe : ℝ[X]}
    (h : IntervalSquareCompletionData d PRe) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (((PRe.eval x) ^ 2 : ℝ) : ℂ) +
        Complement.Interval.intervalComplexForm
          h.squareCertificate.B h.squareCertificate.C x *
          starRingEnd ℂ
            (Complement.Interval.intervalComplexForm
              h.squareCertificate.B h.squareCertificate.C x) =
      1 :=
  Complement.Interval.Witness.real_norm_plus_intervalComplexForm_norm_eq_one
    (h.squareCertificate.toCertificate) hx

/-- The complex polynomial `P := P_re + i B` used in the proof of
[GSLW19, BlockHam.tex:433-435]. -/
noncomputable def completedSignalPolynomial (PRe B : ℝ[X]) : ℂ[X] :=
  realPolynomialToComplex PRe + C Complex.I * realPolynomialToComplex B

/-- The complementary QSP polynomial `Q := i C` used when the real target has
no prescribed real part for `Q` [GSLW19, BlockHam.tex:433-435,544-557]. -/
noncomputable def completedComplementPolynomial (CRe : ℝ[X]) : ℂ[X] :=
  C Complex.I * realPolynomialToComplex CRe

/-- Averaging the completed signal polynomial `P_re + iB` with its
coefficient-conjugate recovers the original real polynomial.  This is the
polynomial identity used when `cor:matchingParity` averages `U_Φ` and
`U_{-Φ}` [GSLW19, BlockHam.tex:851-887]. -/
theorem completedSignalPolynomial_average_conjP (PRe B : ℝ[X]) :
    (1 / 2 : ℂ) • completedSignalPolynomial PRe B +
        (1 / 2 : ℂ) • conjP (completedSignalPolynomial PRe B) =
      realPolynomialToComplex PRe := by
  unfold completedSignalPolynomial
  simp [conjP_add, conjP_mul, Polynomial.smul_eq_C_mul]
  ring_nf
  calc
    C (1 / 2 : ℂ) * realPolynomialToComplex PRe * 2 =
        (C (1 / 2 : ℂ) * 2) * realPolynomialToComplex PRe := by ring
    _ = realPolynomialToComplex PRe := by
      have htwo : (2 : ℂ[X]) = C (2 : ℂ) :=
        (Polynomial.C_eq_natCast (R := ℂ) 2).symm
      rw [htwo]
      have hmul : C (1 / 2 : ℂ) * C (2 : ℂ) = C ((1 / 2 : ℂ) * 2) :=
        (Polynomial.C_mul (a := (1 / 2 : ℂ)) (b := (2 : ℂ))).symm
      rw [hmul]
      simp

/-- The source square certificate gives the polynomial normalization
`P P* + (1-X^2) Q Q* = 1` for `P = P_re+iB` and `Q=iC`
[GSLW19, BlockHam.tex:433-435,475-480]. -/
theorem completedPolynomials_norm {PRe : ℝ[X]}
    (h : Complement.Interval.Certificate (1 - PRe ^ 2)) :
    completedSignalPolynomial PRe h.B * conjP (completedSignalPolynomial PRe h.B) +
        (1 - X ^ 2) *
          (completedComplementPolynomial h.C * conjP (completedComplementPolynomial h.C)) =
      1 := by
  let B : ℝ[X] := h.B
  let CRe : ℝ[X] := h.C
  have hdecomp :
      realPolynomialToComplex (1 - PRe ^ 2) =
        realPolynomialToComplex B ^ 2 + (1 - X ^ 2) * realPolynomialToComplex CRe ^ 2 := by
    calc
      realPolynomialToComplex (1 - PRe ^ 2)
          = realPolynomialToComplex (B ^ 2 + (1 - X ^ 2) * CRe ^ 2) := by
            exact congrArg realPolynomialToComplex (by simpa [B, CRe] using h.eq_decomposition)
      _ = realPolynomialToComplex B ^ 2 + (1 - X ^ 2) * realPolynomialToComplex CRe ^ 2 := by
            simp [pow_two]
  change completedSignalPolynomial PRe B * conjP (completedSignalPolynomial PRe B) +
        (1 - X ^ 2) *
          (completedComplementPolynomial CRe * conjP (completedComplementPolynomial CRe)) =
      1
  have hCI_sq : (C Complex.I : ℂ[X]) ^ 2 = -1 := by
    rw [pow_two, ← Polynomial.C_mul]
    simp [Complex.I_mul_I]
  unfold completedSignalPolynomial completedComplementPolynomial
  simp [conjP_add, conjP_mul, pow_two]
  ring_nf
  rw [hCI_sq]
  ring_nf
  calc
    realPolynomialToComplex PRe ^ 2 + realPolynomialToComplex B ^ 2 -
          X ^ 2 * realPolynomialToComplex CRe ^ 2 + realPolynomialToComplex CRe ^ 2
        = realPolynomialToComplex PRe ^ 2 +
          (realPolynomialToComplex B ^ 2 + (1 - X ^ 2) * realPolynomialToComplex CRe ^ 2) := by
            ring
    _ = realPolynomialToComplex PRe ^ 2 + realPolynomialToComplex (1 - PRe ^ 2) := by
            rw [hdecomp]
    _ = 1 := by
            simp [pow_two]

/-- The interval-square completion data supplies the full reflection-QSP pair
conditions for `P := P_re+iB` and `Q := iC`, following the construction in
[GSLW19, BlockHam.tex:433-435,544-557]. -/
theorem isQSPPair_of_intervalSquareCompletionData {d : ℕ} {PRe : ℝ[X]}
    (h : IntervalSquareCompletionData d PRe) :
    IsQSPPair d
      (completedSignalPolynomial PRe h.squareCertificate.B)
      (completedComplementPolynomial h.squareCertificate.C) := by
  refine isQSPPair_of_coeff ?hPcoeff ?hQcoeff ?hPpar ?hQpar ?hnorm
  · intro m hm
    have hPzero :
        (realPolynomialToComplex PRe).coeff m = 0 :=
      realPolynomialToComplex_coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt h.hypotheses.degree_le hm)
    have hBzero :
        (realPolynomialToComplex h.squareCertificate.B).coeff m = 0 :=
      realPolynomialToComplex_coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt h.squareCertificate.degree_B hm)
    simp [completedSignalPolynomial, hPzero, hBzero]
  · intro m hm
    have hCzero :
        (realPolynomialToComplex h.squareCertificate.C).coeff m = 0 := by
      by_cases hdm : d < m
      · exact realPolynomialToComplex_coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt h.squareCertificate.degree_C hdm)
      · have hmd : m = d := le_antisymm (le_of_not_gt hdm) hm
        by_contra hcoeff
        rw [realPolynomialToComplex, Polynomial.coeff_map] at hcoeff
        have hCcoeff : h.squareCertificate.C.coeff m ≠ 0 := by
          intro hzero
          simp [hzero] at hcoeff
        have hpar := h.squareCertificate.parity_C m hCcoeff
        omega
    simp [completedComplementPolynomial, hCzero]
  · have hPRePar := hasParity_realPolynomialToComplex h.hypotheses.parity
    have hBPar := hasParity_realPolynomialToComplex h.squareCertificate.parity_B
    simpa [completedSignalPolynomial] using hPRePar.add (hBPar.C_mul Complex.I)
  · have hCPar := hasParity_realPolynomialToComplex h.squareCertificate.parity_C
    simpa [completedComplementPolynomial] using hCPar.C_mul Complex.I
  · simpa [Complement.Interval.DegreeParityCertificate.toCertificate] using
      completedPolynomials_norm (PRe := PRe) h.squareCertificate.toCertificate

/-- A source-facing completion certificate for the real-polynomial corollary
[GSLW19, BlockHam.tex:544-557].  It records that a real polynomial `PRe` has a
complex QSP completion `(P,Q)` satisfying the reflection-convention
`IsQSPPair` hypotheses, and that the real part of `P` matches `PRe` on the
source interval.

The existence proof of this certificate is the remaining source-aligned
Lemma-6-to-Corollary-10 work; once present, the phase sequence follows from the
already formalized QSP completeness theorem. -/
structure RealPolynomialCompletion (d : ℕ) (PRe : ℝ[X]) where
  /-- Completed complex signal polynomial whose real part matches `PRe`. -/
  P : ℂ[X]
  /-- Complementary complex polynomial for the reflection-QSP pair. -/
  Q : ℂ[X]
  qsp_pair : IsQSPPair d P Q
  real_part_matches :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → (P.eval (x : ℂ)).re = PRe.eval x
  average_conj_eq :
    (1 / 2 : ℂ) • P + (1 / 2 : ℂ) • conjP P = realPolynomialToComplex PRe

namespace RealPolynomialCompletion

/-- Build the real-polynomial completion from the interval-square certificate
constructed in the proof of [GSLW19, BlockHam.tex:436-480,544-557]. -/
noncomputable def ofIntervalSquareCompletionData {d : ℕ} {PRe : ℝ[X]}
    (h : IntervalSquareCompletionData d PRe) : RealPolynomialCompletion d PRe where
  P := completedSignalPolynomial PRe h.squareCertificate.B
  Q := completedComplementPolynomial h.squareCertificate.C
  qsp_pair := isQSPPair_of_intervalSquareCompletionData h
  real_part_matches := by
    intro x _hx
    simp [completedSignalPolynomial, realPolynomialToComplex_eval_ofReal,
      Polynomial.eval_add, Polynomial.eval_mul]
  average_conj_eq :=
    completedSignalPolynomial_average_conjP PRe h.squareCertificate.B

end RealPolynomialCompletion

/-- The still-internal source-aligned completion target: the hypotheses of
corollary 10 packaged together with the complex completion they imply.  The
nontrivial existence proof is the Lemma-6-through-Corollary-10 chain; this
record keeps downstream QSVT proofs from depending on a source-detached bundle
of assumptions. -/
structure RealBoundedCompletion (d : ℕ) (PRe : ℝ[X]) where
  hypotheses : RealBoundedMatchingParity d PRe
  /-- Complex QSP completion supplied by the source interval-square proof. -/
  completion : RealPolynomialCompletion d PRe

namespace RealBoundedCompletion

/-- Package interval-square data as the real-polynomial completion promised by
Gilyen--Su--Low--Wiebe [GSLW19, BlockHam.tex:544-557]. -/
noncomputable def ofIntervalSquareCompletionData {d : ℕ} {PRe : ℝ[X]}
    (h : IntervalSquareCompletionData d PRe) : RealBoundedCompletion d PRe where
  hypotheses := h.hypotheses
  completion := RealPolynomialCompletion.ofIntervalSquareCompletionData h

/-- Package a source root-class product decomposition as the real-polynomial
completion promised by Gilyen--Su--Low--Wiebe [GSLW19, BlockHam.tex:436-480,
544-557].  This is the direct handoff from the interval-square root
classification layer to the reflection-QSP phase synthesis layer. -/
noncomputable def ofDegreeParityProductDecomposition {d : ℕ} {PRe : ℝ[X]}
    (hP : RealBoundedMatchingParity d PRe)
    (decomp :
      Complement.Interval.DegreeParityProductDecomposition (1 - PRe ^ 2) d) :
    RealBoundedCompletion d PRe :=
  ofIntervalSquareCompletionData
    { hypotheses := hP, squareCertificate := decomp.toCertificate }

/-- Package the source root-class factorization as the real-polynomial
completion promised by Gilyen--Su--Low--Wiebe [GSLW19, BlockHam.tex:436-480,
544-557]. -/
noncomputable def ofSourceRootClassFactorization {d : ℕ} {PRe : ℝ[X]}
    (hP : RealBoundedMatchingParity d PRe)
    (roots :
      Complement.Interval.SourceRootClassFactorization (1 - PRe ^ 2) d) :
    RealBoundedCompletion d PRe :=
  ofDegreeParityProductDecomposition hP roots.toProductDecomposition

end RealBoundedCompletion

/-- The phase certificate delivered by the source `Wx`/reflection-convention QSP
completeness theorem.  This is the phase convention converted to projected
QSVT phases in `cor:refAchievableP` [GSLW19, BlockHam.tex:520-528]. -/
structure PhaseCertificate (d : ℕ) (P Q : ℂ[X]) where
  /-- Initial phase in the reflection-QSP convention. -/
  φ₀ : ℝ
  /-- Remaining reflection-QSP phases. -/
  φs : List ℝ
  length_eq : φs.length = d
  realizes :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      qspW φ₀ φs x = qspMatW P Q x

/-- The top-left scalar entry delivered by a phase certificate.  This is the
entry read in each singular-value invariant block of the QSVT proof
[GSLW19, BlockHam.tex:768-800]. -/
theorem PhaseCertificate.qspW_zero_zero {d : ℕ} {P Q : ℂ[X]}
    (certificate : PhaseCertificate d P Q) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    qspW certificate.φ₀ certificate.φs x 0 0 = P.eval (x : ℂ) := by
  rw [certificate.realizes x hx]
  simp [qspMatW]

/-- A positive-degree source phase certificate has a final phase slot.  The
projected-QSVT local block proof peels off that final phase exactly as in the
source phased-sequence calculation [GSLW19, BlockHam.tex:768-800]. -/
theorem PhaseCertificate.exists_init_last_of_pos {d : ℕ} {P Q : ℂ[X]}
    (certificate : PhaseCertificate d P Q) (hd : 0 < d) :
    ∃ init : List ℝ, ∃ last : ℝ, certificate.φs = init ++ [last] := by
  rcases certificate.φs.eq_nil_or_concat with hnil | ⟨init, last, hsplit⟩
  · have hd0 : d = 0 := by
      simpa [hnil] using certificate.length_eq.symm
    omega
  · exact ⟨init, last, by simpa [List.concat_eq_append] using hsplit⟩

/-- A completion certificate gives an actual reflection-QSP phase certificate
by the existing no-sorry characterization theorem. -/
theorem phaseCertificate_of_completion {d : ℕ} {PRe : ℝ[X]}
    (completion : RealPolynomialCompletion d PRe) :
    Nonempty (PhaseCertificate d completion.P completion.Q) := by
  rcases (ReflectionBasedQuantumSignalProcessing.main_wx d completion.P completion.Q).mp
      completion.qsp_pair with ⟨φ₀, φs, hlen, hrealizes⟩
  exact ⟨⟨φ₀, φs, hlen, hrealizes⟩⟩

/-- A source-aligned real-polynomial completion gives a phase certificate. -/
theorem phaseCertificate_of_realBoundedCompletion {d : ℕ} {PRe : ℝ[X]}
    (h : RealBoundedCompletion d PRe) :
    Nonempty (PhaseCertificate d h.completion.P h.completion.Q) :=
  phaseCertificate_of_completion h.completion

/-- A source-aligned real-polynomial completion supplies a concrete phase
certificate together with the original real polynomial whose real part it
matches [GSLW19, BlockHam.tex:544-557]. -/
structure RealBoundedPhaseCertificate (d : ℕ) (PRe : ℝ[X]) where
  /-- Real-polynomial completion from which the phase certificate was extracted. -/
  completion : RealPolynomialCompletion d PRe
  /-- Reflection-QSP phase certificate for the completed pair. -/
  certificate : PhaseCertificate d completion.P completion.Q

/-- For a real-bounded phase certificate, the real part of the scalar `qspW`
top-left entry is the original real polynomial on `[-1,1]`
[GSLW19, BlockHam.tex:544-557]. -/
theorem RealBoundedPhaseCertificate.qspW_zero_zero_re {d : ℕ} {PRe : ℝ[X]}
    (h : RealBoundedPhaseCertificate d PRe) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (qspW h.certificate.φ₀ h.certificate.φs x 0 0).re = PRe.eval x := by
  rw [h.certificate.qspW_zero_zero hx]
  exact h.completion.real_part_matches x hx

/-- Turn the real bounded completion record into the phase-certificate record
used by projected QSVT. -/
theorem realBoundedPhaseCertificate_of_completion {d : ℕ} {PRe : ℝ[X]}
    (h : RealBoundedCompletion d PRe) :
    Nonempty (RealBoundedPhaseCertificate d PRe) := by
  rcases phaseCertificate_of_realBoundedCompletion h with ⟨certificate⟩
  exact ⟨⟨h.completion, certificate⟩⟩

/-- Interval-square completion data gives a concrete reflection-QSP phase
certificate through the same source path [GSLW19, BlockHam.tex:544-557]. -/
theorem phaseCertificate_of_intervalSquareCompletionData {d : ℕ} {PRe : ℝ[X]}
    (h : IntervalSquareCompletionData d PRe) :
    Nonempty (PhaseCertificate d
      (completedSignalPolynomial PRe h.squareCertificate.B)
      (completedComplementPolynomial h.squareCertificate.C)) := by
  simpa [RealPolynomialCompletion.ofIntervalSquareCompletionData] using
    phaseCertificate_of_completion
      (RealPolynomialCompletion.ofIntervalSquareCompletionData h)

/-- The exact handoff needed from the interval-square root-class proof:
given the source hypotheses of real QSP and the degree/parity square
certificate for `1 - P_re^2`, the reflection-QSP phase certificate follows.
This isolates the remaining Gilyén Lemma-6-to-Corollary-10 existence work from
the downstream QSVT proof path [GSLW19, BlockHam.tex:436-480,544-557]. -/
theorem phaseCertificate_of_degreeParityCertificate {d : ℕ} {PRe : ℝ[X]}
    (hP : RealBoundedMatchingParity d PRe)
    (cert : Complement.Interval.DegreeParityCertificate (1 - PRe ^ 2) d) :
    Nonempty (PhaseCertificate d
      (completedSignalPolynomial PRe cert.B)
      (completedComplementPolynomial cert.C)) :=
  phaseCertificate_of_intervalSquareCompletionData
    { hypotheses := hP, squareCertificate := cert }

/-- Source root-class product decompositions are the exact remaining
input needed for the real-polynomial QSP corollary [GSLW19,
BlockHam.tex:436-480,544-557]. -/
theorem phaseCertificate_of_degreeParityProductDecomposition {d : ℕ} {PRe : ℝ[X]}
    (hP : RealBoundedMatchingParity d PRe)
    (decomp :
      Complement.Interval.DegreeParityProductDecomposition (1 - PRe ^ 2) d) :
    Nonempty (PhaseCertificate d
      (completedSignalPolynomial PRe decomp.toCertificate.B)
      (completedComplementPolynomial decomp.toCertificate.C)) :=
  phaseCertificate_of_intervalSquareCompletionData
    { hypotheses := hP, squareCertificate := decomp.toCertificate }

/-- A source root-class factorization gives the reflection-QSP phase
certificate used downstream by projected QSVT [GSLW19, BlockHam.tex:436-480,
544-557]. -/
theorem phaseCertificate_of_sourceRootClassFactorization {d : ℕ} {PRe : ℝ[X]}
    (hP : RealBoundedMatchingParity d PRe)
    (roots :
      Complement.Interval.SourceRootClassFactorization (1 - PRe ^ 2) d) :
    Nonempty (PhaseCertificate d
      (completedSignalPolynomial PRe roots.toCertificate.B)
      (completedComplementPolynomial roots.toCertificate.C)) :=
  phaseCertificate_of_degreeParityProductDecomposition hP roots.toProductDecomposition

/-- Same handoff as `phaseCertificate_of_sourceRootClassFactorization`, stated
with the source square target attached to the real-polynomial hypotheses.  This
is the form downstream projected QSVT uses after the interval-square theorem
constructs the source root-class factorization [GSLW19, BlockHam.tex:436-480,
544-557]. -/
theorem phaseCertificate_of_realBoundedRootFactorization {d : ℕ} {PRe : ℝ[X]}
    (hP : RealBoundedMatchingParity d PRe)
    (roots :
      Complement.Interval.SourceRootClassFactorization
        (RealBoundedMatchingParity.squareTarget PRe) d) :
    Nonempty (PhaseCertificate d
      (completedSignalPolynomial PRe roots.toCertificate.B)
      (completedComplementPolynomial roots.toCertificate.C)) := by
  simpa [RealBoundedMatchingParity.squareTarget] using
    phaseCertificate_of_sourceRootClassFactorization hP roots

/-- Source root-class factorization for the square target gives the full
real-bounded phase-certificate package consumed by projected QSVT [GSLW19,
BlockHam.tex:436-480,544-557]. -/
theorem realBoundedPhaseCertificate_of_sourceRootClassFactorization
    {d : ℕ} {PRe : ℝ[X]} (hP : RealBoundedMatchingParity d PRe)
    (roots :
      Complement.Interval.SourceRootClassFactorization
        (RealBoundedMatchingParity.squareTarget PRe) d) :
    Nonempty (RealBoundedPhaseCertificate d PRe) := by
  let completionData : IntervalSquareCompletionData d PRe :=
    { hypotheses := hP
      squareCertificate := roots.toCertificate }
  exact realBoundedPhaseCertificate_of_completion
    (RealBoundedCompletion.ofIntervalSquareCompletionData completionData)

/-- Choose the real-bounded phase certificate determined by a source root-class
factorization.  This is a noncomputable extraction from the source-aligned
existence theorem, not an additional assumption [GSLW19, BlockHam.tex:436-480,
544-557]. -/
noncomputable def chooseRealBoundedPhaseCertificateOfSourceRootClassFactorization
    {d : ℕ} {PRe : ℝ[X]} (hP : RealBoundedMatchingParity d PRe)
    (roots :
      Complement.Interval.SourceRootClassFactorization
        (RealBoundedMatchingParity.squareTarget PRe) d) :
    RealBoundedPhaseCertificate d PRe :=
  Classical.choice
    (realBoundedPhaseCertificate_of_sourceRootClassFactorization hP roots)

/-- A completed source root-coverage package gives the real-bounded phase
certificate consumed by projected QSVT [GSLW19, BlockHam.tex:436-480,
544-557]. -/
theorem realBoundedPhaseCertificate_of_sourceRootClassCoverage
    {d : ℕ} {PRe : ℝ[X]} (hP : RealBoundedMatchingParity d PRe)
    {data :
      Complement.Interval.SourceRootProductData
        (RealBoundedMatchingParity.squareTarget PRe)}
    (coverage : Complement.Interval.SourceRootClassCoverage data d) :
    Nonempty (RealBoundedPhaseCertificate d PRe) :=
  realBoundedPhaseCertificate_of_sourceRootClassFactorization hP
    coverage.toSourceRootClassFactorization

/-- Choose the real-bounded phase certificate determined by completed
source-root coverage. -/
noncomputable def chooseRealBoundedPhaseCertificateOfSourceRootClassCoverage
    {d : ℕ} {PRe : ℝ[X]} (hP : RealBoundedMatchingParity d PRe)
    {data :
      Complement.Interval.SourceRootProductData
        (RealBoundedMatchingParity.squareTarget PRe)}
    (coverage : Complement.Interval.SourceRootClassCoverage data d) :
    RealBoundedPhaseCertificate d PRe :=
  Classical.choice
    (realBoundedPhaseCertificate_of_sourceRootClassCoverage hP coverage)

/-- Product identity plus the source degree bound are enough to choose the
real-bounded phase certificate: unit padding supplies the remaining degree.
This is the final handoff shape for the source root-class construction in
[GSLW19, BlockHam.tex:469-480,544-557]. -/
theorem realBoundedPhaseCertificate_of_sourceRootProductAndDegreeLe
    {d : ℕ} {PRe : ℝ[X]} (hP : RealBoundedMatchingParity d PRe)
    {data :
      Complement.Interval.SourceRootProductData
        (RealBoundedMatchingParity.squareTarget PRe)}
    (constant : ℝ) (constant_nonnegative : 0 ≤ constant)
    (hproduct :
      RealBoundedMatchingParity.squareTarget PRe =
        Polynomial.C constant *
          (Polynomial.X : ℝ[X]) ^ (2 * data.zeroRootPairs) *
          Complement.Interval.DegreeParityFactorCertificate.productPoly
            (data.interiorRealRootPairParameters.map
              Complement.Interval.DegreeParityFactorCertificate.interiorRealRootPair) *
          Complement.Interval.DegreeParityFactorCertificate.productPoly
            (data.outsideRealRoots.map (fun s =>
              Complement.Interval.DegreeParityFactorCertificate.realRoot s.value s.outside)) *
          Complement.Interval.DegreeParityFactorCertificate.productPoly
            (data.imaginaryRootParameters.map
              Complement.Interval.DegreeParityFactorCertificate.imaginaryRoot) *
          Complement.Interval.DegreeParityFactorCertificate.productPoly
            (data.complexRootParameters.map (fun z =>
              Complement.Interval.DegreeParityFactorCertificate.complexRoot z.1 z.2)))
    (hdegree_le : data.rootClassDegree ≤ d) :
    Nonempty (RealBoundedPhaseCertificate d PRe) :=
  realBoundedPhaseCertificate_of_sourceRootClassCoverage hP
    (Complement.Interval.SourceRootClassCoverage.ofProductEqAndDegreeLe
      constant constant_nonnegative hproduct hdegree_le)

/-- Noncomputably choose the phase certificate from the final source product
identity and degree bound [GSLW19, BlockHam.tex:469-480,544-557]. -/
noncomputable def chooseRealBoundedPhaseCertificateOfSourceRootProductAndDegreeLe
    {d : ℕ} {PRe : ℝ[X]} (hP : RealBoundedMatchingParity d PRe)
    {data :
      Complement.Interval.SourceRootProductData
        (RealBoundedMatchingParity.squareTarget PRe)}
    (constant : ℝ) (constant_nonnegative : 0 ≤ constant)
    (hproduct :
      RealBoundedMatchingParity.squareTarget PRe =
        Polynomial.C constant *
          (Polynomial.X : ℝ[X]) ^ (2 * data.zeroRootPairs) *
          Complement.Interval.DegreeParityFactorCertificate.productPoly
            (data.interiorRealRootPairParameters.map
              Complement.Interval.DegreeParityFactorCertificate.interiorRealRootPair) *
          Complement.Interval.DegreeParityFactorCertificate.productPoly
            (data.outsideRealRoots.map (fun s =>
              Complement.Interval.DegreeParityFactorCertificate.realRoot s.value s.outside)) *
          Complement.Interval.DegreeParityFactorCertificate.productPoly
            (data.imaginaryRootParameters.map
              Complement.Interval.DegreeParityFactorCertificate.imaginaryRoot) *
          Complement.Interval.DegreeParityFactorCertificate.productPoly
            (data.complexRootParameters.map (fun z =>
              Complement.Interval.DegreeParityFactorCertificate.complexRoot z.1 z.2)))
    (hdegree_le : data.rootClassDegree ≤ d) :
    RealBoundedPhaseCertificate d PRe :=
  Classical.choice
    (realBoundedPhaseCertificate_of_sourceRootProductAndDegreeLe hP
      constant constant_nonnegative hproduct hdegree_le)

/-- Final handoff from the canonical source data of `1 - P_re^2`: once the
source proof supplies the product identity and degree bound, the real-polynomial
phase certificate follows [GSLW19, BlockHam.tex:436-480,544-557]. -/
theorem realBoundedPhaseCertificate_ofSquareTargetProductAndDegreeLe
    {d : ℕ} {PRe : ℝ[X]} (hP : RealBoundedMatchingParity d PRe)
    (constant : ℝ) (constant_nonnegative : 0 ≤ constant) :
    let data :=
      (RealBoundedMatchingParity.squareTarget_sourceHypotheses hP).rootProductData
    (hproduct :
      RealBoundedMatchingParity.squareTarget PRe =
        Polynomial.C constant *
          (Polynomial.X : ℝ[X]) ^
            (2 * data.zeroRootPairs) *
          Complement.Interval.DegreeParityFactorCertificate.productPoly
            (data.interiorRealRootPairParameters.map
                Complement.Interval.DegreeParityFactorCertificate.interiorRealRootPair) *
          Complement.Interval.DegreeParityFactorCertificate.productPoly
            (data.outsideRealRoots.map (fun s =>
                Complement.Interval.DegreeParityFactorCertificate.realRoot s.value s.outside)) *
          Complement.Interval.DegreeParityFactorCertificate.productPoly
            (data.imaginaryRootParameters.map
                Complement.Interval.DegreeParityFactorCertificate.imaginaryRoot) *
          Complement.Interval.DegreeParityFactorCertificate.productPoly
            (data.complexRootParameters.map (fun z =>
                Complement.Interval.DegreeParityFactorCertificate.complexRoot z.1 z.2))) →
    data.rootClassDegree ≤ d →
    Nonempty (RealBoundedPhaseCertificate d PRe) := by
  dsimp
  intro hproduct hdegree_le
  exact realBoundedPhaseCertificate_of_sourceRootClassFactorization hP
    (Complement.Interval.SourceHypotheses.factorizationOfProductEqAndDegreeLe
      (RealBoundedMatchingParity.squareTarget_sourceHypotheses hP)
      constant constant_nonnegative hproduct hdegree_le)

/-- End-to-end handoff from the Gilyén Lemma-6 interval-square decomposition
to the real-polynomial QSP phase certificate.  This is the compact
Lemma-6-through-Corollary-10 interface: the root-class factorization is now
constructed internally from the source hypotheses of `1 - P_re^2`
[GSLW19, BlockHam.tex:436-480,544-557]. -/
theorem realBoundedPhaseCertificate_of_sourceHypotheses
    {d : ℕ} {PRe : ℝ[X]} (hP : RealBoundedMatchingParity d PRe) :
    Nonempty (RealBoundedPhaseCertificate d PRe) :=
  realBoundedPhaseCertificate_of_sourceRootClassFactorization hP
    ((RealBoundedMatchingParity.squareTarget_sourceHypotheses hP).factorizationOfSourceProduct)

/-- Noncomputably choose the real-bounded phase certificate from the completed
source-aligned interval-square proof [GSLW19, BlockHam.tex:436-480,544-557]. -/
noncomputable def chooseRealBoundedPhaseCertificateOfSourceHypotheses
    {d : ℕ} {PRe : ℝ[X]} (hP : RealBoundedMatchingParity d PRe) :
    RealBoundedPhaseCertificate d PRe :=
  Classical.choice (realBoundedPhaseCertificate_of_sourceHypotheses hP)

/-- Boundary-case end-to-end handoff for the source chain: when the square target
`1 - P_re^2` is constant, the source root-class construction immediately gives
the real-bounded phase certificate [GSLW19, BlockHam.tex:436-480,544-557]. -/
noncomputable def chooseRealBoundedPhaseCertificateOfSquareTargetNatDegreeZero
    {d : ℕ} {PRe : ℝ[X]} (hP : RealBoundedMatchingParity d PRe)
    (hdeg : (RealBoundedMatchingParity.squareTarget PRe).natDegree = 0) :
    RealBoundedPhaseCertificate d PRe :=
  chooseRealBoundedPhaseCertificateOfSourceRootClassFactorization hP
    (Complement.Interval.SourceHypotheses.factorizationOfNatDegreeEqZero
      (RealBoundedMatchingParity.squareTarget_sourceHypotheses hP) hdeg)

end ReflectionQSPPhaseSynthesis

end QuantumAlg
