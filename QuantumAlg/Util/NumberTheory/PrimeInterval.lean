/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.NumberTheory.WeightedChebyshev

import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Explicit primes in the top quarter of a dyadic interval

This module converts elementary explicit Chebyshev estimates into the
prime-count denominator needed by same-bit RSA key generation.  The final
bound decays like `1 / b`, as required by the prime number theorem; no fixed
positive fraction of all `b`-bit integers is asserted.

The stronger explicit theta estimates in [BKL+20,
sharper-bounds-psi-theta-May2020-resubmittedMathComp.tex:290-312,555-557]
support the same interval conclusion.  The proof below is independently
kernel-checked from the elementary weighted Chebyshev argument.
-/

section

namespace QuantumAlg
namespace NumberTheory

open Finset Real
open scoped Chebyshev

/-- A conservative, asymptotically valid lower bound for primes in the top
quarter below `2^b`. -/
def topQuarterPrimeCountLowerBound (b : ℕ) : ℕ :=
  2 ^ b / (16 * b)

/-- Exponential growth dominates the quadratic error term from bit length 512
onward. -/
private theorem hundred_mul_sq_le_two_pow {b : ℕ} (hb : 32 ≤ b) :
    (100 * b) ^ 2 ≤ 2 ^ b := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ b hb ih =>
      calc
        (100 * (b + 1)) ^ 2 ≤ 2 * (100 * b) ^ 2 := by
          nlinarith
        _ ≤ 2 * 2 ^ b := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (b + 1) := by rw [pow_succ]; omega

/-- The theta mass of a prime interval is at most its cardinality times the
largest logarithmic weight in the interval. -/
private theorem theta_sub_le_primeCount_mul_log {m n : ℕ} (hmn : m ≤ n) :
    Chebyshev.theta n - Chebyshev.theta m ≤
      ((Nat.primeCounting n - Nat.primeCounting m : ℕ) : ℝ) * log n := by
  have hsubset : Nat.primesLE m ⊆ Nat.primesLE n :=
    Nat.primesLE_mono hmn
  rw [Chebyshev.theta_eq_sum_primesLE_log,
    Chebyshev.theta_eq_sum_primesLE_log, ← Finset.sum_sdiff_eq_sub hsubset]
  calc
    ∑ p ∈ Nat.primesLE n \ Nat.primesLE m, log p
        ≤ ∑ _p ∈ Nat.primesLE n \ Nat.primesLE m, log n := by
          apply Finset.sum_le_sum
          intro p hp
          have hpn : p ∈ Nat.primesLE n := (Finset.mem_sdiff.mp hp).1
          exact log_le_log
            (by exact_mod_cast (Nat.prime_of_mem_primesLE hpn).pos)
            (by exact_mod_cast Nat.le_of_mem_primesLE hpn)
    _ = ((Nat.primeCounting n - Nat.primeCounting m : ℕ) : ℝ) * log n := by
      rw [Finset.sum_const, nsmul_eq_mul,
        Finset.card_sdiff_of_subset hsubset]
      simp

/-- For every `b ≥ 512`, the top quarter of the `b`-bit dyadic interval
contains at least `2^b / (16b)` primes. -/
theorem topQuarterPrimeCount (b : ℕ) (hb : 512 ≤ b) :
    topQuarterPrimeCountLowerBound b ≤
      Nat.primeCounting (2 ^ b) -
        Nat.primeCounting (3 * 2 ^ (b - 2)) := by
  let x : ℕ := 2 ^ b
  let y : ℕ := 3 * 2 ^ (b - 2)
  have hb2 : 2 ≤ b := by omega
  have hpowSplit : x = 4 * 2 ^ (b - 2) := by
    dsimp [x]
    calc
      2 ^ b = 2 ^ ((b - 2) + 2) := by congr 1; omega
      _ = 4 * 2 ^ (b - 2) := by rw [pow_add]; ring
  have hyx : y ≤ x := by
    dsimp [y]
    rw [hpowSplit]
    omega
  have hsquareNat : (100 * b) ^ 2 ≤ x := by
    exact hundred_mul_sq_le_two_pow (by omega)
  have hsquareReal : (((100 * b : ℕ) : ℝ) ^ 2) ≤ (x : ℝ) := by
    exact_mod_cast hsquareNat
  have hsqrtLower : ((100 * b : ℕ) : ℝ) ≤ √(x : ℝ) :=
    Real.le_sqrt_of_sq_le hsquareReal
  have hlogEq : log (x : ℝ) = (b : ℝ) * log 2 := by
    dsimp [x]
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hlogLeBits : log (x : ℝ) ≤ (b : ℝ) := by
    rw [hlogEq]
    have hlogTwo : log 2 ≤ (1 : ℝ) :=
      Real.log_two_lt_d9.le.trans (by norm_num)
    simpa using mul_le_mul_of_nonneg_left
      hlogTwo (Nat.cast_nonneg b)
  have hlogSqrt : log (x : ℝ) ≤ √(x : ℝ) / 100 := by
    norm_num at hsqrtLower
    linarith
  have hsqrtSq : (√(x : ℝ)) ^ 2 = (x : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrtLarge : (100 : ℝ) ≤ √(x : ℝ) := by
    have hbReal : (512 : ℝ) ≤ b := by exact_mod_cast hb
    norm_num at hsqrtLower
    nlinarith
  have hsqrtLinear : √(x : ℝ) ≤ (x : ℝ) / 100 := by
    nlinarith
  have hbasePow : 51840 ≤ x := by
    have h32 : 51840 ≤ 2 ^ (32 : ℕ) := by norm_num
    exact h32.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hquarterLarge : (38880 : ℝ) ≤ 3 * (x : ℝ) / 4 := by
    have hbaseReal : (51840 : ℝ) ≤ x := by exact_mod_cast hbasePow
    nlinarith
  have htheta := WeightedChebyshev.theta_top_quarter_mass
    (x : ℝ) (by positivity) hquarterLarge hsqrtLinear hlogSqrt
  have hyReal : (y : ℝ) = 3 * (x : ℝ) / 4 := by
    dsimp [y]
    rw [hpowSplit]
    push_cast
    ring
  rw [← hyReal] at htheta
  have hthetaCount := theta_sub_le_primeCount_mul_log hyx
  have hcountLog :
      (x : ℝ) / 16 ≤
        ((Nat.primeCounting x - Nat.primeCounting y : ℕ) : ℝ) * log x :=
    htheta.trans hthetaCount
  have hcountBits :
      (x : ℝ) / 16 ≤
        ((Nat.primeCounting x - Nat.primeCounting y : ℕ) : ℝ) * b := by
    exact hcountLog.trans (mul_le_mul_of_nonneg_left hlogLeBits (by positivity))
  have hnat :
      x ≤ (Nat.primeCounting x - Nat.primeCounting y) * (16 * b) := by
    have hreal :
        (x : ℝ) ≤
          ((Nat.primeCounting x - Nat.primeCounting y : ℕ) : ℝ) *
            ((16 * b : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast hreal
  have hdiv :
      x / (16 * b) ≤
        ((Nat.primeCounting x - Nat.primeCounting y) * (16 * b)) /
          (16 * b) :=
    Nat.div_le_div_right hnat
  simpa [topQuarterPrimeCountLowerBound, x, y,
    show 16 * b ≠ 0 by omega] using hdiv

end NumberTheory
end QuantumAlg

end
