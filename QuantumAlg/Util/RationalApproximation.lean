/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Rational-approximation uniqueness helpers

This module contains quantum-free number-theory lemmas used by order recovery.
They isolate the uniqueness step: once an approximation has been reduced to a
cleared denominator inequality smaller than one, the corresponding reduced
fraction is unique.

The intended order-finding use is Shor's continued-fraction recovery step:
a measured ratio close to `d/r` determines the unique reduced fraction with
bounded denominator [Sho95, source.tex:1614-1633] [dW19, qcnotes.tex:2293-2301,
2316-2362].
-/

@[expose] public section

namespace QuantumAlg

namespace RationalApproximation

/-- If two natural numbers have real distance strictly less than one, they are
equal. This is the integer discreteness step used after clearing denominators
in rational-approximation uniqueness arguments. -/
theorem nat_eq_of_abs_cast_sub_lt_one {a b : ℕ}
    (h : |((a : ℝ) - (b : ℝ))| < 1) :
    a = b := by
  by_contra hne
  have hne_int : (a : ℤ) - (b : ℤ) ≠ 0 := by
    intro hzero
    exact hne (by exact_mod_cast sub_eq_zero.mp hzero)
  have hone_int : (1 : ℤ) ≤ |(a : ℤ) - (b : ℤ)| :=
    Int.one_le_abs hne_int
  have hone_real : (1 : ℝ) ≤ |((a : ℝ) - (b : ℝ))| := by
    exact_mod_cast hone_int
  exact not_lt_of_ge hone_real h

/-- Reduced natural fractions are unique: if `p/q` and `s/r` are both reduced,
with positive denominators, and have equal cross products, then the numerators
and denominators agree. -/
theorem reducedFraction_eq_of_cross_mul {p q s r : ℕ}
    (hq : 0 < q) (hr : 0 < r)
    (hpq : Nat.Coprime p q) (hsr : Nat.Coprime s r)
    (hcross : p * r = s * q) :
    p = s ∧ q = r := by
  have hq_dvd_r : q ∣ r := by
    have hdiv : q ∣ p * r := by
      rw [hcross]
      exact dvd_mul_left q s
    exact (hpq.symm.dvd_mul_left).mp hdiv
  have hr_dvd_q : r ∣ q := by
    have hdiv : r ∣ s * q := by
      rw [← hcross]
      exact dvd_mul_left r p
    exact (hsr.symm.dvd_mul_left).mp hdiv
  have hqr : q = r :=
    le_antisymm (Nat.le_of_dvd hr hq_dvd_r) (Nat.le_of_dvd hq hr_dvd_q)
  have hps : p = s := by
    have hmul : p * r = s * r := by
      simpa [hqr] using hcross
    exact mul_right_cancel₀ hr.ne' hmul
  exact ⟨hps, hqr⟩

/-- Cleared-error uniqueness for reduced natural fractions. The hypothesis is
the post-clearing form of a rational approximation bound: the cross-product
distance is strictly smaller than one, hence it is zero, and reduced-fraction
uniqueness finishes the argument. -/
theorem reducedFraction_unique_of_cleared_error_lt_one {p q s r : ℕ}
    (hq : 0 < q) (hr : 0 < r)
    (hpq : Nat.Coprime p q) (hsr : Nat.Coprime s r)
    (h : |((p * r : ℝ) - (s * q : ℝ))| < 1) :
    p = s ∧ q = r := by
  have hcross : p * r = s * q :=
    nat_eq_of_abs_cast_sub_lt_one (by simpa [Nat.cast_mul] using h)
  exact reducedFraction_eq_of_cross_mul hq hr hpq hsr hcross

/-- The rational denominator of a reduced fraction of natural numbers is the
given denominator. -/
theorem reducedNatFraction_den {p q : ℕ}
    (hq : 0 < q) (hpq : Nat.Coprime p q) :
    (((p : ℚ) / (q : ℚ)).den = q) := by
  rw [Rat.natCast_div_eq_divInt, Rat.den_divInt]
  simp only [Int.natCast_eq_zero, Int.natAbs_natCast, Int.gcd_natCast_natCast,
    hq.ne']
  rw [Nat.gcd_comm q p, hpq.gcd_eq_one]
  simp

/-- Legendre's continued-fraction criterion for a reduced fraction of natural
numbers, stated with the unreduced denominator parameter used by order recovery.
The result uses Mathlib's `Real.convergent` API. -/
theorem reducedFraction_eq_convergent_of_legendre {ξ : ℝ} {p q : ℕ}
    (hq : 0 < q) (hpq : Nat.Coprime p q)
    (happrox :
      |ξ - (((p : ℚ) / (q : ℚ) : ℚ) : ℝ)| < 1 / (2 * (q : ℝ) ^ 2)) :
    ∃ n, (p : ℚ) / (q : ℚ) = ξ.convergent n := by
  have hden := reducedNatFraction_den (p := p) (q := q) hq hpq
  have happrox' :
      |ξ - (((p : ℚ) / (q : ℚ) : ℚ) : ℝ)| <
        1 / (2 * (((p : ℚ) / (q : ℚ)).den : ℝ) ^ 2) := by
    simpa [hden] using happrox
  exact Real.exists_rat_eq_convergent happrox'

/-- Legendre recovery for the order-finding phase-estimate shape. If a dyadic
or real phase estimate `ξ` is within `1/(2r^2)` of the reduced fraction `s/r`,
then `s/r` appears as a continued-fraction convergent of `ξ`, and the recovered
convergent denominator is exactly `r`. -/
theorem denominatorRecovery_of_phaseEstimate {ξ : ℝ} {s r : ℕ}
    (hr : 0 < r) (hsr : Nat.Coprime s r)
    (happrox :
      |ξ - (((s : ℚ) / (r : ℚ) : ℚ) : ℝ)| < 1 / (2 * (r : ℝ) ^ 2)) :
    ∃ n, (s : ℚ) / (r : ℚ) = ξ.convergent n ∧
      (ξ.convergent n).den = r := by
  obtain ⟨n, hn⟩ :=
    reducedFraction_eq_convergent_of_legendre
      (ξ := ξ) (p := s) (q := r) hr hsr happrox
  refine ⟨n, hn, ?_⟩
  rw [← hn]
  exact reducedNatFraction_den (p := s) (q := r) hr hsr

/-- If a reduced candidate fraction satisfies Legendre's bound and also passes
the cleared-error uniqueness test against the true reduced fraction, then the
candidate is one of the continued-fraction convergents and its denominator is
the true denominator. The separate validation that a concrete continued-fraction
search returns this candidate is intentionally outside this theorem. -/
private theorem continuedFraction_denominatorRecovery_of_cleared_error_lt_one {ξ : ℝ}
    {p q s r : ℕ}
    (hq : 0 < q) (hr : 0 < r)
    (hpq : Nat.Coprime p q) (hsr : Nat.Coprime s r)
    (happrox :
      |ξ - (((p : ℚ) / (q : ℚ) : ℚ) : ℝ)| < 1 / (2 * (q : ℝ) ^ 2))
    (hcleared : |((p * r : ℝ) - (s * q : ℝ))| < 1) :
    ∃ n, (p : ℚ) / (q : ℚ) = ξ.convergent n ∧ q = r := by
  obtain ⟨n, hn⟩ :=
    reducedFraction_eq_convergent_of_legendre
      (ξ := ξ) (p := p) (q := q) hq hpq happrox
  exact ⟨n, hn, (reducedFraction_unique_of_cleared_error_lt_one
    hq hr hpq hsr hcleared).2⟩

end RationalApproximation

end QuantumAlg
