/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.PrimeCounting
import QuantumAlg.Init
import all QuantumAlg.Util.NumberTheory.CommonDivisorTail
import all QuantumAlg.Util.NumberTheory.Cyclic.Order
import all QuantumAlg.Util.NumberTheory.NinthPowerTable

/-!
# Explicit divisor-count bounds

The main reduction in this module turns independently certified bounds for
each prime-power factor into one bound for the divisor count of an integer.
This keeps finite small-prime computation separate from the general
factorization argument.
-/

section

namespace QuantumAlg
namespace NumberTheory

/-- Integer correction budget for one prime below `256`.  Each nonzero entry
is the ceiling of the largest binary logarithm of
`(a+1)^8 / p^a`; exponents beyond eleven are covered by the uniform ratio
step proved below. -/
def smallPrimeDivisorCorrectionBits : Nat → Nat
  | 2 => 18
  | 3 => 13
  | 5 => 10
  | 7 => 8
  | 11 => 6
  | 13 => 6
  | 17 => 5
  | 19 => 5
  | 23 => 4
  | 29 => 4
  | 31 => 4
  | 37 => 3
  | 41 => 3
  | 43 => 3
  | 47 => 3
  | 53 => 3
  | 59 => 3
  | 61 => 3
  | 67 => 2
  | 71 => 2
  | 73 => 2
  | 79 => 2
  | 83 => 2
  | 89 => 2
  | 97 => 2
  | 101 => 2
  | 103 => 2
  | 107 => 2
  | 109 => 2
  | 113 => 2
  | 127 => 2
  | 131 => 1
  | 137 => 1
  | 139 => 1
  | 149 => 1
  | 151 => 1
  | 157 => 1
  | 163 => 1
  | 167 => 1
  | 173 => 1
  | 179 => 1
  | 181 => 1
  | 191 => 1
  | 193 => 1
  | 197 => 1
  | 199 => 1
  | 211 => 1
  | 223 => 1
  | 227 => 1
  | 229 => 1
  | 233 => 1
  | 239 => 1
  | 241 => 1
  | 251 => 1
  | _ => 0

/-- Large primes need no correction because `(a+1)^8 ≤ 256^a ≤ p^a`.
Small primes use the finite table above. -/
def primeDivisorCorrectionBits (p : Nat) : Nat :=
  if p < 256 then smallPrimeDivisorCorrectionBits p else 0

/-- Elementary exponential estimate used for primes at least `256`. -/
theorem add_one_le_two_pow (a : Nat) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
      calc
        a + 1 + 1 ≤ 2 * (a + 1) := by omega
        _ ≤ 2 * 2 ^ a := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (a + 1) := by simp [pow_succ, Nat.mul_comm]

/-- Once `a ≥ 11`, increasing the exponent multiplies `(a+1)^8` by at most
two. -/
theorem add_two_pow_eight_le_two_mul_add_one_pow_eight
    {a : Nat} (ha : 11 ≤ a) :
    (a + 2) ^ 8 ≤ 2 * (a + 1) ^ 8 := by
  have hlinear : 12 * (a + 2) ≤ 13 * (a + 1) := by omega
  have hpow := Nat.pow_le_pow_left hlinear 8
  have hconstant : 13 ^ 8 ≤ 2 * 12 ^ 8 := by norm_num
  have hscaled :
      12 ^ 8 * (a + 2) ^ 8 ≤ 12 ^ 8 * (2 * (a + 1) ^ 8) := by
    calc
      12 ^ 8 * (a + 2) ^ 8 = (12 * (a + 2)) ^ 8 := by
        rw [Nat.mul_pow]
      _ ≤ (13 * (a + 1)) ^ 8 := hpow
      _ = 13 ^ 8 * (a + 1) ^ 8 := by rw [Nat.mul_pow]
      _ ≤ (2 * 12 ^ 8) * (a + 1) ^ 8 :=
        Nat.mul_le_mul_right _ hconstant
      _ = 12 ^ 8 * (2 * (a + 1) ^ 8) := by ring
  omega

/-- Checking the first twelve exponents is enough for every prime at least
two, because the local ratio grows by at most two while `p^a` grows by `p`. -/
theorem prime_power_divisor_bound_of_first_twelve
    {p correction : Nat} (hp : 2 ≤ p)
    (hsmall : ∀ a < 12,
      (a + 1) ^ 8 ≤ 2 ^ correction * p ^ a) :
    ∀ a, (a + 1) ^ 8 ≤ 2 ^ correction * p ^ a := by
  intro a
  by_cases ha : a < 12
  · exact hsmall a ha
  have ha11 : 11 ≤ a := by omega
  let offset := a - 11
  have haEq : a = 11 + offset := by
    simp only [offset]
    omega
  rw [haEq]
  induction offset with
  | zero => exact hsmall 11 (by omega)
  | succ offset ih =>
      calc
        (11 + (offset + 1) + 1) ^ 8 =
            (11 + offset + 2) ^ 8 := by
          simp only [Nat.add_assoc]
        _ ≤ 2 * (11 + offset + 1) ^ 8 :=
          add_two_pow_eight_le_two_mul_add_one_pow_eight (by omega)
        _ ≤ p * (2 ^ correction * p ^ (11 + offset)) :=
          Nat.mul_le_mul hp ih
        _ = 2 ^ correction * p ^ (11 + (offset + 1)) := by
          rw [show 11 + (offset + 1) = (11 + offset) + 1 by omega,
            pow_succ]
          ac_rfl

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks all 54 small primes and twelve exponents at once.
set_option maxRecDepth 100000 in
/-- Kernel-checked finite part of the small-prime correction certificate. -/
theorem small_prime_power_divisor_table :
    ∀ p ∈ Nat.primesBelow 256, ∀ a ∈ Finset.range 12,
      (a + 1) ^ 8 ≤
        2 ^ primeDivisorCorrectionBits p * p ^ a := by
  decide

/-- Every prime power satisfies its entry in the correction table. -/
theorem prime_power_divisor_bound
    {p : Nat} (hp : p.Prime) (a : Nat) :
    (a + 1) ^ 8 ≤
      2 ^ primeDivisorCorrectionBits p * p ^ a := by
  by_cases hlarge : 256 ≤ p
  · have hcorrection : primeDivisorCorrectionBits p = 0 := by
      simp [primeDivisorCorrectionBits, Nat.not_lt_of_ge hlarge]
    rw [hcorrection, pow_zero, one_mul]
    calc
      (a + 1) ^ 8 ≤ (2 ^ a) ^ 8 :=
        Nat.pow_le_pow_left (add_one_le_two_pow a) 8
      _ = 256 ^ a := by
        change (2 ^ a) ^ 8 = (2 ^ 8) ^ a
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ p ^ a := Nat.pow_le_pow_left hlarge a
  · apply prime_power_divisor_bound_of_first_twelve hp.two_le
    intro exponent hexponent
    have hpLt : p < 256 := Nat.lt_of_not_ge hlarge
    exact small_prime_power_divisor_table p
      (Nat.mem_primesBelow.mpr ⟨hpLt, hp⟩) exponent
      (Finset.mem_range.mpr hexponent)

set_option maxHeartbeats 8000000 in
-- Kernel reduction enumerates `Nat.primesBelow 256` and sums the table.
set_option maxRecDepth 100000 in
/-- The complete small-prime table consumes 153 correction bits. -/
theorem sum_small_prime_divisor_corrections :
    ∑ p ∈ Nat.primesBelow 256, primeDivisorCorrectionBits p = 153 := by
  decide

/-- The correction budget over the prime factors of any integer is at most
the complete 153-bit small-prime table. -/
theorem sum_primeFactor_divisor_corrections_le (n : Nat) :
    ∑ p ∈ n.primeFactors, primeDivisorCorrectionBits p ≤ 153 := by
  let smallFactors := n.primeFactors.filter (fun p => p < 256)
  have hsum :
      ∑ p ∈ n.primeFactors, primeDivisorCorrectionBits p =
        ∑ p ∈ smallFactors, primeDivisorCorrectionBits p := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hpNotLt : ¬p < 256 := by
      intro hpLt
      exact hnot (Finset.mem_filter.mpr ⟨hp, hpLt⟩)
    have hpGe : 256 ≤ p := Nat.le_of_not_gt hpNotLt
    simp [primeDivisorCorrectionBits, Nat.not_lt_of_ge hpGe]
  rw [hsum, ← sum_small_prime_divisor_corrections]
  apply Finset.sum_le_sum_of_subset
  intro p hp
  have hpParts := Finset.mem_filter.mp hp
  exact Nat.mem_primesBelow.mpr
    ⟨hpParts.2, Nat.prime_of_mem_primeFactors hpParts.1⟩

/-- Local prime-power correction bounds multiply to a global eighth-power
bound for the divisor count.  The exponent budget `correction` may depend on
the prime, but its sum over the distinct prime factors must be bounded by
`totalCorrection`.

The eighth power is chosen because the same-bit RSA application needs a
uniform divisor estimate of size `n^(1/8)` up to an explicit constant. -/
theorem card_divisors_pow_eight_le_of_local
    {n : Nat} (hn : n ≠ 0)
    (correction : Nat → Nat) (totalCorrection : Nat)
    (hlocal : ∀ p ∈ n.primeFactors,
      (n.factorization p + 1) ^ 8 ≤
        2 ^ correction p * p ^ n.factorization p)
    (hcorrection :
      ∑ p ∈ n.primeFactors, correction p ≤ totalCorrection) :
    n.divisors.card ^ 8 ≤ 2 ^ totalCorrection * n := by
  rw [Nat.card_divisors hn]
  calc
    (n.primeFactors.prod (n.factorization · + 1)) ^ 8 =
        ∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ 8 := by
      simp only [Finset.prod_pow]
    _ ≤ ∏ p ∈ n.primeFactors,
        (2 ^ correction p * p ^ n.factorization p) := by
      exact Finset.prod_le_prod (fun _p _hp => Nat.zero_le _)
        hlocal
    _ = 2 ^ (∑ p ∈ n.primeFactors, correction p) * n := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      rw [← Nat.prod_factorization_eq_prod_primeFactors]
      rw [Nat.prod_factorization_pow_eq_self hn]
    _ ≤ 2 ^ totalCorrection * n := by
      exact Nat.mul_le_mul_right n
        (Nat.pow_le_pow_right (by decide : 0 < 2) hcorrection)

/-- Global explicit divisor-count certificate. -/
theorem card_divisors_pow_eight_le {n : Nat} (hn : n ≠ 0) :
    n.divisors.card ^ 8 ≤ 2 ^ 153 * n := by
  apply card_divisors_pow_eight_le_of_local hn
    primeDivisorCorrectionBits 153
  · intro p hp
    exact prime_power_divisor_bound
      (Nat.prime_of_mem_primeFactors hp) (n.factorization p)
  · exact sum_primeFactor_divisor_corrections_le n

/-! ## Sharper ninth-power certificate -/

/-- Once `a ≥ 12`, increasing the exponent multiplies `(a+1)^9` by at
most two. -/
theorem add_two_pow_nine_le_two_mul_add_one_pow_nine
    {a : Nat} (ha : 12 ≤ a) :
    (a + 2) ^ 9 ≤ 2 * (a + 1) ^ 9 := by
  have hlinear : 13 * (a + 2) ≤ 14 * (a + 1) := by omega
  have hpow := Nat.pow_le_pow_left hlinear 9
  have hconstant : 14 ^ 9 ≤ 2 * 13 ^ 9 := by norm_num
  have hscaled :
      13 ^ 9 * (a + 2) ^ 9 ≤ 13 ^ 9 * (2 * (a + 1) ^ 9) := by
    calc
      13 ^ 9 * (a + 2) ^ 9 = (13 * (a + 2)) ^ 9 := by
        rw [Nat.mul_pow]
      _ ≤ (14 * (a + 1)) ^ 9 := hpow
      _ = 14 ^ 9 * (a + 1) ^ 9 := by rw [Nat.mul_pow]
      _ ≤ (2 * 13 ^ 9) * (a + 1) ^ 9 :=
        Nat.mul_le_mul_right _ hconstant
      _ = 13 ^ 9 * (2 * (a + 1) ^ 9) := by ring
  omega

/-- The first thirteen exponents determine the ninth-power bound for all
exponents. -/
theorem prime_power_nine_bound_of_first_thirteen
    {p correction : Nat} (hp : 2 ≤ p)
    (hsmall : ∀ a < 13,
      (a + 1) ^ 9 ≤ 2 ^ correction * p ^ a) :
    ∀ a, (a + 1) ^ 9 ≤ 2 ^ correction * p ^ a := by
  intro a
  by_cases ha : a < 13
  · exact hsmall a ha
  have ha12 : 12 ≤ a := by omega
  let offset := a - 12
  have haEq : a = 12 + offset := by
    simp only [offset]
    omega
  rw [haEq]
  induction offset with
  | zero => exact hsmall 12 (by omega)
  | succ offset ih =>
      calc
        (12 + (offset + 1) + 1) ^ 9 =
            (12 + offset + 2) ^ 9 := by
          simp only [Nat.add_assoc]
        _ ≤ 2 * (12 + offset + 1) ^ 9 :=
          add_two_pow_nine_le_two_mul_add_one_pow_nine (by omega)
        _ ≤ p * (2 ^ correction * p ^ (12 + offset)) :=
          Nat.mul_le_mul hp ih
        _ = 2 ^ correction * p ^ (12 + (offset + 1)) := by
          rw [show 12 + (offset + 1) = (12 + offset) + 1 by omega,
            pow_succ]
          ac_rfl

/-- A finite check at the least base of one correction interval controls
every larger base in that interval. -/
theorem prime_power_nine_bound_from_lower
    {p lower correction : Nat} (hp : 2 ≤ p) (hlower : lower ≤ p)
    (hcorrection : primePowerNineCorrectionBits p = correction)
    (hsmall : ∀ a < 13,
      (a + 1) ^ 9 ≤ 2 ^ correction * lower ^ a) :
    ∀ a, (a + 1) ^ 9 ≤ 2 ^ primePowerNineCorrectionBits p * p ^ a := by
  apply prime_power_nine_bound_of_first_thirteen hp
  intro a ha
  rw [hcorrection]
  exact (hsmall a ha).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlower a))

/- Each closed certificate checks the thirteen exponents at the least base of
one interval.  Keeping them separate produces small kernel proof terms and
lets the general theorem use monotonicity in the prime base. -/

theorem prime_power_nine_threshold_two :
    ∀ a < 13, (a + 1) ^ 9 ≤ 2 ^ 22 * 2 ^ a := by decide

theorem prime_power_nine_threshold_three :
    ∀ a < 13, (a + 1) ^ 9 ≤ 2 ^ 16 * 3 ^ a := by decide

theorem prime_power_nine_threshold_five :
    ∀ a < 13, (a + 1) ^ 9 ≤ 2 ^ 12 * 5 ^ a := by decide

theorem prime_power_nine_threshold_seven :
    ∀ a < 13, (a + 1) ^ 9 ≤ 2 ^ 10 * 7 ^ a := by decide

theorem prime_power_nine_threshold_eleven :
    ∀ a < 13, (a + 1) ^ 9 ≤ 2 ^ 8 * 11 ^ a := by decide

theorem prime_power_nine_threshold_thirteen :
    ∀ a < 13, (a + 1) ^ 9 ≤ 2 ^ 7 * 13 ^ a := by decide

theorem prime_power_nine_threshold_nineteen :
    ∀ a < 13, (a + 1) ^ 9 ≤ 2 ^ 6 * 19 ^ a := by decide

theorem prime_power_nine_threshold_twentyNine :
    ∀ a < 13, (a + 1) ^ 9 ≤ 2 ^ 5 * 29 ^ a := by decide

theorem prime_power_nine_threshold_thirtySeven :
    ∀ a < 13, (a + 1) ^ 9 ≤ 2 ^ 4 * 37 ^ a := by decide

theorem prime_power_nine_threshold_sixtySeven :
    ∀ a < 13, (a + 1) ^ 9 ≤ 2 ^ 3 * 67 ^ a := by decide

theorem prime_power_nine_threshold_oneThirtyOne :
    ∀ a < 13, (a + 1) ^ 9 ≤ 2 ^ 2 * 131 ^ a := by decide

theorem prime_power_nine_threshold_twoFiftySeven :
    ∀ a < 13, (a + 1) ^ 9 ≤ 2 ^ 1 * 257 ^ a := by decide

/-- Every prime power satisfies the ninth-power correction table. -/
theorem prime_power_nine_bound
    {p : Nat} (hp : p.Prime) (a : Nat) :
    (a + 1) ^ 9 ≤ 2 ^ primePowerNineCorrectionBits p * p ^ a := by
  by_cases hlarge : 512 ≤ p
  · have hcorrection : primePowerNineCorrectionBits p = 0 := by
      unfold primePowerNineCorrectionBits
      simp only [if_neg (by omega : ¬ p < 3),
        if_neg (by omega : ¬ p < 5),
        if_neg (by omega : ¬ p < 7),
        if_neg (by omega : ¬ p < 11),
        if_neg (by omega : ¬ p < 13),
        if_neg (by omega : ¬ p < 19),
        if_neg (by omega : ¬ p < 29),
        if_neg (by omega : ¬ p < 37),
        if_neg (by omega : ¬ p < 67),
        if_neg (by omega : ¬ p < 131),
        if_neg (by omega : ¬ p < 257),
        if_neg (by omega : ¬ p < 512)]
    rw [hcorrection, pow_zero, one_mul]
    calc
      (a + 1) ^ 9 ≤ (2 ^ a) ^ 9 :=
        Nat.pow_le_pow_left (add_one_le_two_pow a) 9
      _ = 512 ^ a := by
        change (2 ^ a) ^ 9 = (2 ^ 9) ^ a
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ p ^ a := Nat.pow_le_pow_left hlarge a
  · have hp512 : p < 512 := Nat.lt_of_not_ge hlarge
    by_cases hp3 : p < 3
    · apply prime_power_nine_bound_from_lower (lower := 2) (correction := 22)
        hp.two_le hp.two_le
        (by simp [primePowerNineCorrectionBits, hp3])
      exact prime_power_nine_threshold_two
    by_cases hp5 : p < 5
    · apply prime_power_nine_bound_from_lower (lower := 3) (correction := 16)
        hp.two_le (by omega : 3 ≤ p)
        (by simp [primePowerNineCorrectionBits, hp3, hp5])
      exact prime_power_nine_threshold_three
    by_cases hp7 : p < 7
    · apply prime_power_nine_bound_from_lower (lower := 5) (correction := 12)
        hp.two_le (by omega : 5 ≤ p)
        (by simp [primePowerNineCorrectionBits, hp3, hp5, hp7])
      exact prime_power_nine_threshold_five
    by_cases hp11 : p < 11
    · apply prime_power_nine_bound_from_lower (lower := 7) (correction := 10)
        hp.two_le (by omega : 7 ≤ p)
        (by simp [primePowerNineCorrectionBits, hp3, hp5, hp7, hp11])
      exact prime_power_nine_threshold_seven
    by_cases hp13 : p < 13
    · apply prime_power_nine_bound_from_lower (lower := 11) (correction := 8)
        hp.two_le (by omega : 11 ≤ p)
        (by simp [primePowerNineCorrectionBits, hp3, hp5, hp7, hp11, hp13])
      exact prime_power_nine_threshold_eleven
    by_cases hp19 : p < 19
    · apply prime_power_nine_bound_from_lower (lower := 13) (correction := 7)
        hp.two_le (by omega : 13 ≤ p)
        (by simp [primePowerNineCorrectionBits, hp3, hp5, hp7, hp11, hp13,
          hp19])
      exact prime_power_nine_threshold_thirteen
    by_cases hp29 : p < 29
    · apply prime_power_nine_bound_from_lower (lower := 19) (correction := 6)
        hp.two_le (by omega : 19 ≤ p)
        (by simp [primePowerNineCorrectionBits, hp3, hp5, hp7, hp11, hp13,
          hp19, hp29])
      exact prime_power_nine_threshold_nineteen
    by_cases hp37 : p < 37
    · apply prime_power_nine_bound_from_lower (lower := 29) (correction := 5)
        hp.two_le (by omega : 29 ≤ p)
        (by simp [primePowerNineCorrectionBits, hp3, hp5, hp7, hp11, hp13,
          hp19, hp29, hp37])
      exact prime_power_nine_threshold_twentyNine
    by_cases hp67 : p < 67
    · apply prime_power_nine_bound_from_lower (lower := 37) (correction := 4)
        hp.two_le (by omega : 37 ≤ p)
        (by simp [primePowerNineCorrectionBits, hp3, hp5, hp7, hp11, hp13,
          hp19, hp29, hp37, hp67])
      exact prime_power_nine_threshold_thirtySeven
    by_cases hp131 : p < 131
    · apply prime_power_nine_bound_from_lower (lower := 67) (correction := 3)
        hp.two_le (by omega : 67 ≤ p)
        (by simp [primePowerNineCorrectionBits, hp3, hp5, hp7, hp11, hp13,
          hp19, hp29, hp37, hp67, hp131])
      exact prime_power_nine_threshold_sixtySeven
    by_cases hp257 : p < 257
    · apply prime_power_nine_bound_from_lower (lower := 131) (correction := 2)
        hp.two_le (by omega : 131 ≤ p)
        (by simp [primePowerNineCorrectionBits, hp3, hp5, hp7, hp11, hp13,
          hp19, hp29, hp37, hp67, hp131, hp257])
      exact prime_power_nine_threshold_oneThirtyOne
    · apply prime_power_nine_bound_from_lower (lower := 257) (correction := 1)
        hp.two_le (by omega : 257 ≤ p)
        (by simp [primePowerNineCorrectionBits, hp3, hp5, hp7, hp11, hp13,
          hp19, hp29, hp37, hp67, hp131, hp257, hp512])
      exact prime_power_nine_threshold_twoFiftySeven

/-- The ninth-power correction budget over any integer's prime factors is at
most 276 bits. -/
theorem sum_primeFactor_nine_corrections_le (n : Nat) :
    ∑ p ∈ n.primeFactors, primePowerNineCorrectionBits p ≤ 276 := by
  let smallFactors := n.primeFactors.filter (fun p => p < 512)
  have hsum :
      ∑ p ∈ n.primeFactors, primePowerNineCorrectionBits p =
        ∑ p ∈ smallFactors, primePowerNineCorrectionBits p := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hpNotLt : ¬p < 512 := by
      intro hpLt
      exact hnot (Finset.mem_filter.mpr ⟨hp, hpLt⟩)
    have hpGe : 512 ≤ p := Nat.le_of_not_gt hpNotLt
    unfold primePowerNineCorrectionBits
    simp only [if_neg (by omega : ¬ p < 3),
      if_neg (by omega : ¬ p < 5),
      if_neg (by omega : ¬ p < 7),
      if_neg (by omega : ¬ p < 11),
      if_neg (by omega : ¬ p < 13),
      if_neg (by omega : ¬ p < 19),
      if_neg (by omega : ¬ p < 29),
      if_neg (by omega : ¬ p < 37),
      if_neg (by omega : ¬ p < 67),
      if_neg (by omega : ¬ p < 131),
      if_neg (by omega : ¬ p < 257),
      if_neg (by omega : ¬ p < 512)]
  rw [hsum, ← sum_wheelCandidate_nine_corrections]
  apply Finset.sum_le_sum_of_subset
  intro p hp
  have hpParts := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpParts.2,
    prime_wheelCandidate (Nat.prime_of_mem_primeFactors hpParts.1)⟩

/-- Local ninth-power bounds multiply to a global divisor-count bound. -/
theorem card_divisors_pow_nine_le_of_local
    {n : Nat} (hn : n ≠ 0)
    (correction : Nat → Nat) (totalCorrection : Nat)
    (hlocal : ∀ p ∈ n.primeFactors,
      (n.factorization p + 1) ^ 9 ≤
        2 ^ correction p * p ^ n.factorization p)
    (hcorrection :
      ∑ p ∈ n.primeFactors, correction p ≤ totalCorrection) :
    n.divisors.card ^ 9 ≤ 2 ^ totalCorrection * n := by
  rw [Nat.card_divisors hn]
  calc
    (n.primeFactors.prod (n.factorization · + 1)) ^ 9 =
        ∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ 9 := by
      simp only [Finset.prod_pow]
    _ ≤ ∏ p ∈ n.primeFactors,
        (2 ^ correction p * p ^ n.factorization p) := by
      exact Finset.prod_le_prod (fun _p _hp => Nat.zero_le _) hlocal
    _ = 2 ^ (∑ p ∈ n.primeFactors, correction p) * n := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      rw [← Nat.prod_factorization_eq_prod_primeFactors]
      rw [Nat.prod_factorization_pow_eq_self hn]
    _ ≤ 2 ^ totalCorrection * n := by
      exact Nat.mul_le_mul_right n
        (Nat.pow_le_pow_right (by decide : 0 < 2) hcorrection)

/-- Sharper global explicit divisor-count certificate. -/
theorem card_divisors_pow_nine_le {n : Nat} (hn : n ≠ 0) :
    n.divisors.card ^ 9 ≤ 2 ^ 276 * n := by
  apply card_divisors_pow_nine_le_of_local hn
    primePowerNineCorrectionBits 276
  · intro p hp
    exact prime_power_nine_bound
      (Nat.prime_of_mem_primeFactors hp) (n.factorization p)
  · exact sum_primeFactor_nine_corrections_le n

/-- Binary exponent sufficient to bound the divisor count of every positive
integer below `2^bits`. -/
def divisorCountBoundBits (bits : Nat) : Nat :=
  (bits + 276) ⌈/⌉ 9

/-- Every positive integer below `2^bits` has strictly fewer than
`2^divisorCountBoundBits bits` divisors. -/
theorem card_divisors_lt_two_pow_divisorCountBoundBits
    {n bits : Nat} (hn : n ≠ 0) (hnLt : n < 2 ^ bits) :
    n.divisors.card < 2 ^ divisorCountBoundBits bits := by
  have hceil :
      bits + 276 ≤ 9 * divisorCountBoundBits bits := by
    exact (ceilDiv_le_iff_le_mul (a := 9) (b := bits + 276)
      (c := divisorCountBoundBits bits) (by decide)).1 le_rfl
  have hglobal := card_divisors_pow_nine_le hn
  have hupper : n.divisors.card ^ 9 < 2 ^ (bits + 276) := by
    calc
      n.divisors.card ^ 9 ≤ 2 ^ 276 * n := hglobal
      _ < 2 ^ 276 * 2 ^ bits :=
        (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ 276)).2 hnLt
      _ = 2 ^ (bits + 276) := by
        rw [← pow_add]
        ac_rfl
  by_contra hnot
  have hcard : 2 ^ divisorCountBoundBits bits ≤ n.divisors.card :=
    Nat.le_of_not_gt hnot
  have hpow :
      (2 ^ divisorCountBoundBits bits) ^ 9 ≤
        n.divisors.card ^ 9 := Nat.pow_le_pow_left hcard 9
  have hlower :
      2 ^ (bits + 276) ≤
        (2 ^ divisorCountBoundBits bits) ^ 9 := by
    calc
      2 ^ (bits + 276) ≤
          2 ^ (9 * divisorCountBoundBits bits) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) hceil
      _ = (2 ^ divisorCountBoundBits bits) ^ 9 := by
        rw [← pow_mul, Nat.mul_comm]
  exact (Nat.not_lt_of_ge (hlower.trans hpow)) hupper

end NumberTheory
end QuantumAlg

end
