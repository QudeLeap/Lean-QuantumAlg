/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Mathlib.Data.ENNReal.Basic

import QuantumAlg.Init
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Size

/-!
# Shared RSA failure budgets and exact retry calibration

RSA-style endpoints encode the public failure parameter as a positive rational
number.  The exact repetition multiplier is selected here, once, by the
closed-form ceiling used by both factoring routes.  Algorithm modules consume
that value directly in their circuit/run syntax; no caller supplies a retry
count or a resource profile.
-/

section

namespace QuantumAlg
namespace Factoring

noncomputable section

/-- Positive rational target failure budget `failureNumerator /
failureDenominator`. -/
public structure FailureBudget where
  /-- Positive numerator of the rational target failure probability. -/
  failureNumerator : Nat
  /-- Positive denominator of the rational target failure probability. -/
  failureDenominator : Nat
deriving DecidableEq

namespace FailureBudget

/-- The public failure parameter lies in `(0, 1]`. -/
public structure WellFormed (budget : FailureBudget) : Prop where
  numerator_pos : 0 < budget.failureNumerator
  denominator_pos : 0 < budget.failureDenominator
  numerator_le_denominator :
    budget.failureNumerator ≤ budget.failureDenominator

/-- A rational failure rate strictly between zero and one.  This is the
calibration domain for an independently repeated attempt. -/
structure StrictlyWellFormed (failure : FailureBudget) : Prop
    extends WellFormed failure where
  numerator_lt_denominator :
    failure.failureNumerator < failure.failureDenominator

/-- Real value of the encoded public failure parameter. -/
public def value (budget : FailureBudget) : Real :=
  (budget.failureNumerator : Real) / budget.failureDenominator

/-- Public success threshold `1 - eta`. -/
public def successThreshold (budget : FailureBudget) : ENNReal :=
  ENNReal.ofReal (1 - budget.value)

/-- Real logarithmic exponent for reducing an arbitrary certified one-attempt
failure rate to the requested public failure budget. -/
def retryExponentFor (failure budget : FailureBudget) : Real :=
  Real.log
      ((budget.failureDenominator : Real) /
        budget.failureNumerator) /
    Real.log
      ((failure.failureDenominator : Real) /
        failure.failureNumerator)

/-- Exact ceiling-form retry count for an arbitrary certified one-attempt
failure rate.  The count is data computed from the two rational rates, never a
caller-supplied witness. -/
def retryCountFor (failure budget : FailureBudget) : Nat :=
  max 1 (Nat.ceil (retryExponentFor failure budget))

/-- Real logarithmic exponent for reducing a one-third failure probability to
the requested public failure budget. -/
def retryExponent (budget : FailureBudget) : Real :=
  Real.log
      ((budget.failureDenominator : Real) /
        budget.failureNumerator) /
    Real.log 3

/-- Exact, internally selected retry/amplification count.  `max 1` preserves a
real execution even at the boundary `eta = 1`; the second argument is the
literal ceiling closed form required by the public resource theorem. -/
def retryCount (budget : FailureBudget) : Nat :=
  max 1 (Nat.ceil (retryExponent budget))

theorem retryCount_pos (budget : FailureBudget) : 0 < retryCount budget := by
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

@[simp] theorem retryCount_ne_zero (budget : FailureBudget) :
    retryCount budget ≠ 0 :=
  Nat.ne_of_gt (retryCount_pos budget)

theorem value_pos (budget : FailureBudget) (hbudget : WellFormed budget) :
    0 < budget.value := by
  unfold value
  exact div_pos (by exact_mod_cast hbudget.numerator_pos)
    (by exact_mod_cast hbudget.denominator_pos)

theorem value_nonneg (budget : FailureBudget) (hbudget : WellFormed budget) :
    0 ≤ budget.value :=
  (value_pos budget hbudget).le

theorem value_le_one (budget : FailureBudget) (hbudget : WellFormed budget) :
    budget.value ≤ 1 := by
  unfold value
  apply (div_le_one (by exact_mod_cast hbudget.denominator_pos)).2
  exact_mod_cast hbudget.numerator_le_denominator

/-- The logarithmic size of a well-formed rational failure target is bounded
by the binary encoding length of its denominator. -/
theorem retryLogRatio_le_denominatorSize
    (budget : FailureBudget) (hbudget : budget.WellFormed) :
    Real.log
        ((budget.failureDenominator : Real) /
          budget.failureNumerator) ≤
      (Nat.size budget.failureDenominator : Real) := by
  have hnum : (0 : Real) < budget.failureNumerator := by
    exact_mod_cast hbudget.numerator_pos
  have hden : (0 : Real) < budget.failureDenominator := by
    exact_mod_cast hbudget.denominator_pos
  have hdenPow :
      (budget.failureDenominator : Real) <
        (2 : Real) ^ Nat.size budget.failureDenominator := by
    exact_mod_cast Nat.lt_size_self budget.failureDenominator
  have hlogTwo : Real.log (2 : Real) ≤ 1 := by
    have h := Real.log_lt_sub_one_of_pos
      (show (0 : Real) < 2 by norm_num)
      (show (2 : Real) ≠ 1 by norm_num)
    norm_num at h
    exact h.le
  calc
    Real.log
        ((budget.failureDenominator : Real) /
          budget.failureNumerator) =
        Real.log budget.failureDenominator -
          Real.log budget.failureNumerator :=
      Real.log_div hden.ne' hnum.ne'
    _ ≤ Real.log budget.failureDenominator :=
      sub_le_self _ (Real.log_natCast_nonneg _)
    _ ≤ Real.log
        ((2 : Real) ^ Nat.size budget.failureDenominator) :=
      (Real.log_lt_log hden hdenPow).le
    _ = (Nat.size budget.failureDenominator : Real) *
        Real.log 2 := by
      rw [Real.log_pow]
    _ ≤ (Nat.size budget.failureDenominator : Real) * 1 :=
      mul_le_mul_of_nonneg_left hlogTwo (by positivity)
    _ = Nat.size budget.failureDenominator := by ring

theorem retryCountFor_pos (failure budget : FailureBudget) :
    0 < retryCountFor failure budget := by
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

@[simp] theorem retryCountFor_ne_zero (failure budget : FailureBudget) :
    retryCountFor failure budget ≠ 0 :=
  Nat.ne_of_gt (retryCountFor_pos failure budget)

/-- The literal generic ceiling is at least its real logarithmic exponent. -/
theorem retryExponentFor_le_retryCountFor (failure budget : FailureBudget) :
    retryExponentFor failure budget ≤
      (retryCountFor failure budget : Real) := by
  have hceil :
      retryExponentFor failure budget ≤
        (Nat.ceil (retryExponentFor failure budget) : Real) :=
    Nat.le_ceil _
  have hmax :
      Nat.ceil (retryExponentFor failure budget) ≤
        retryCountFor failure budget := by
    exact Nat.le_max_right _ _
  exact hceil.trans (by exact_mod_cast hmax)

/-- The generic retry count is the least positive natural number above the
exact logarithmic calibration exponent. -/
theorem retryCountFor_le_of_one_le_of_exponent_le
    (failure budget : FailureBudget) {count : Nat}
    (hone : 1 ≤ count)
    (hexponent : retryExponentFor failure budget ≤ (count : Real)) :
    retryCountFor failure budget ≤ count := by
  unfold retryCountFor
  apply max_le hone
  exact Nat.ceil_le.mpr hexponent

/-- The exact generic ceiling reduces the certified one-attempt failure rate
below the requested rational target. -/
theorem retryFailurePowerForReal_le (failure budget : FailureBudget)
    (hfailure : StrictlyWellFormed failure)
    (hbudget : WellFormed budget) :
    failure.value ^ retryCountFor failure budget ≤ budget.value := by
  have hfailureNum : (0 : Real) < failure.failureNumerator := by
    exact_mod_cast hfailure.numerator_pos
  have hfailureDen : (0 : Real) < failure.failureDenominator := by
    exact_mod_cast hfailure.denominator_pos
  have hbudgetNum : (0 : Real) < budget.failureNumerator := by
    exact_mod_cast hbudget.numerator_pos
  have hbudgetDen : (0 : Real) < budget.failureDenominator := by
    exact_mod_cast hbudget.denominator_pos
  have hfailureRatioPos :
      0 < (failure.failureDenominator : Real) /
        failure.failureNumerator := by
    positivity
  have hfailureRatioOne :
      1 < (failure.failureDenominator : Real) /
        failure.failureNumerator := by
    rw [lt_div_iff₀ hfailureNum]
    norm_num
    exact_mod_cast hfailure.numerator_lt_denominator
  have hbudgetRatioPos :
      0 < (budget.failureDenominator : Real) /
        budget.failureNumerator := by
    positivity
  have hlogFailureRatioPos :
      0 < Real.log
        ((failure.failureDenominator : Real) /
          failure.failureNumerator) :=
    Real.log_pos hfailureRatioOne
  have hlog :
      Real.log
          ((budget.failureDenominator : Real) /
            budget.failureNumerator) ≤
        (retryCountFor failure budget : Real) *
          Real.log
            ((failure.failureDenominator : Real) /
              failure.failureNumerator) := by
    have hexponent := retryExponentFor_le_retryCountFor failure budget
    rw [retryExponentFor] at hexponent
    exact (div_le_iff₀ hlogFailureRatioPos).mp hexponent
  have hratio_le_pow :
      (budget.failureDenominator : Real) / budget.failureNumerator ≤
        ((failure.failureDenominator : Real) /
          failure.failureNumerator) ^ retryCountFor failure budget := by
    calc
      (budget.failureDenominator : Real) / budget.failureNumerator =
          Real.exp
            (Real.log
              ((budget.failureDenominator : Real) /
                budget.failureNumerator)) :=
        (Real.exp_log hbudgetRatioPos).symm
      _ ≤ Real.exp
          ((retryCountFor failure budget : Real) *
            Real.log
              ((failure.failureDenominator : Real) /
                failure.failureNumerator)) :=
        Real.exp_le_exp.mpr hlog
      _ = ((failure.failureDenominator : Real) /
          failure.failureNumerator) ^ retryCountFor failure budget := by
        rw [← Real.log_pow]
        exact Real.exp_log (pow_pos hfailureRatioPos _)
  have hfailureValue :
      failure.value =
        1 / ((failure.failureDenominator : Real) /
          failure.failureNumerator) := by
    unfold value
    field_simp
  rw [hfailureValue, one_div_pow]
  calc
    1 / (((failure.failureDenominator : Real) /
          failure.failureNumerator) ^ retryCountFor failure budget) ≤
        1 / ((budget.failureDenominator : Real) /
          budget.failureNumerator) :=
      one_div_le_one_div_of_le hbudgetRatioPos hratio_le_pow
    _ = budget.value := by
      unfold value
      field_simp

theorem retryFailurePowerFor_le (failure budget : FailureBudget)
    (hfailure : StrictlyWellFormed failure)
    (hbudget : WellFormed budget) :
    (ENNReal.ofReal failure.value) ^ retryCountFor failure budget ≤
      ENNReal.ofReal budget.value := by
  rw [← ENNReal.ofReal_pow (value_nonneg failure hfailure.toWellFormed)]
  exact ENNReal.ofReal_le_ofReal
    (retryFailurePowerForReal_le failure budget hfailure hbudget)

/-- Increasing the internally computed retry count can only decrease a
certified failure power. -/
theorem retryFailurePowerFor_le_of_count (failure budget : FailureBudget)
    (hfailure : StrictlyWellFormed failure)
    (hbudget : WellFormed budget) {count : Nat}
    (hcount : retryCountFor failure budget ≤ count) :
    (ENNReal.ofReal failure.value) ^ count ≤ ENNReal.ofReal budget.value := by
  calc
    (ENNReal.ofReal failure.value) ^ count ≤
        (ENNReal.ofReal failure.value) ^ retryCountFor failure budget := by
      exact pow_le_pow_right_of_le_one' (by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal
          (value_le_one failure hfailure.toWellFormed)) hcount
    _ ≤ ENNReal.ofReal budget.value :=
      retryFailurePowerFor_le failure budget hfailure hbudget

/-- The literal ceiling in `retryCount` is at least the real logarithmic
exponent from which it is selected. -/
theorem retryExponent_le_retryCount (budget : FailureBudget) :
    retryExponent budget ≤ (retryCount budget : Real) := by
  have hceil :
      retryExponent budget ≤ (Nat.ceil (retryExponent budget) : Real) :=
    Nat.le_ceil _
  have hmax :
      Nat.ceil (retryExponent budget) ≤ retryCount budget := by
    exact Nat.le_max_right _ _
  exact hceil.trans (by exact_mod_cast hmax)

/-- The base-three geometric failure after the internally selected retry
count is at most the public rational failure budget. -/
theorem retryFailurePowerReal_le (budget : FailureBudget)
    (hbudget : WellFormed budget) :
    ((1 : Real) / 3) ^ retryCount budget ≤ budget.value := by
  have hnum : (0 : Real) < budget.failureNumerator := by
    exact_mod_cast hbudget.numerator_pos
  have hden : (0 : Real) < budget.failureDenominator := by
    exact_mod_cast hbudget.denominator_pos
  have hratio_pos :
      0 < (budget.failureDenominator : Real) /
        budget.failureNumerator := by
    positivity
  have hlog_three_pos : 0 < Real.log (3 : Real) :=
    Real.log_pos (by norm_num)
  have hlog :
      Real.log
          ((budget.failureDenominator : Real) /
            budget.failureNumerator) ≤
        (retryCount budget : Real) * Real.log 3 := by
    have hexponent := retryExponent_le_retryCount budget
    rw [retryExponent] at hexponent
    exact (div_le_iff₀ hlog_three_pos).mp hexponent
  have hratio_le_pow :
      (budget.failureDenominator : Real) /
          budget.failureNumerator ≤
        (3 : Real) ^ retryCount budget := by
    calc
      (budget.failureDenominator : Real) / budget.failureNumerator =
          Real.exp
            (Real.log
              ((budget.failureDenominator : Real) /
                budget.failureNumerator)) :=
        (Real.exp_log hratio_pos).symm
      _ ≤ Real.exp ((retryCount budget : Real) * Real.log 3) :=
        Real.exp_le_exp.mpr hlog
      _ = (3 : Real) ^ retryCount budget := by
        rw [← Real.log_pow]
        exact Real.exp_log (pow_pos (by norm_num) _)
  calc
    ((1 : Real) / 3) ^ retryCount budget =
        1 / ((3 : Real) ^ retryCount budget) := by
      rw [one_div_pow]
    _ ≤ 1 /
        ((budget.failureDenominator : Real) /
          budget.failureNumerator) :=
      one_div_le_one_div_of_le hratio_pos hratio_le_pow
    _ = budget.value := by
      unfold value
      field_simp

theorem retryFailurePower_le (budget : FailureBudget)
    (hbudget : WellFormed budget) :
    (ENNReal.ofReal ((1 : Real) / 3)) ^ retryCount budget ≤
      ENNReal.ofReal budget.value := by
  rw [← ENNReal.ofReal_pow (by norm_num : (0 : Real) ≤ 1 / 3)]
  exact ENNReal.ofReal_le_ofReal (retryFailurePowerReal_le budget hbudget)

theorem twoThirds_eq_one_sub_oneThird :
    ENNReal.ofReal ((2 : Real) / 3) =
      1 - ENNReal.ofReal ((1 : Real) / 3) := by
  rw [← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (by norm_num : (0 : Real) ≤ 1 / 3)]
  norm_num

theorem one_sub_twoThirds_eq_oneThird :
    1 - ENNReal.ofReal ((2 : Real) / 3) =
      ENNReal.ofReal ((1 : Real) / 3) := by
  rw [← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (by norm_num : (0 : Real) ≤ 2 / 3)]
  norm_num

/-- The public `1 - eta` target lies below the exact independent-retry
success bound obtained from a per-attempt two-thirds floor. -/
theorem successThreshold_le_one_sub_retryFailurePower
    (budget : FailureBudget) (hbudget : WellFormed budget) :
    successThreshold budget ≤
      1 - (ENNReal.ofReal ((1 : Real) / 3)) ^ retryCount budget := by
  rw [successThreshold, ENNReal.ofReal_sub _ (value_nonneg budget hbudget),
    ENNReal.ofReal_one]
  exact tsub_le_tsub_left (retryFailurePower_le budget hbudget) 1

/-- At least one retry preserves the per-attempt two-thirds floor. -/
theorem twoThirds_le_one_sub_retryFailurePower (budget : FailureBudget) :
    ENNReal.ofReal ((2 : Real) / 3) ≤
      1 - (ENNReal.ofReal ((1 : Real) / 3)) ^ retryCount budget := by
  have hfailure :
      (ENNReal.ofReal ((1 : Real) / 3)) ^ retryCount budget ≤
        ENNReal.ofReal ((1 : Real) / 3) := by
    exact pow_le_of_le_one (by positivity) (by norm_num)
      (retryCount_ne_zero budget)
  have hcomplement :
      ENNReal.ofReal ((2 : Real) / 3) =
        1 - ENNReal.ofReal ((1 : Real) / 3) :=
    twoThirds_eq_one_sub_oneThird
  rw [hcomplement]
  exact tsub_le_tsub_left hfailure 1

/-- The fixed one-third target used to retain the public two-thirds success
floor independently of the caller's requested failure budget. -/
def oneThird : FailureBudget where
  failureNumerator := 1
  failureDenominator := 3

theorem oneThird_wellFormed : oneThird.WellFormed := by
  constructor <;> norm_num [oneThird]

@[simp] theorem oneThird_value : oneThird.value = (1 : Real) / 3 := by
  norm_num [oneThird, value]

/-- Binary failure budget `2^-k`. -/
def binary (k : Nat) : FailureBudget where
  failureNumerator := 1
  failureDenominator := 2 ^ k

theorem binary_wellFormed (k : Nat) : (binary k).WellFormed where
  numerator_pos := Nat.zero_lt_one
  denominator_pos := Nat.two_pow_pos k
  numerator_le_denominator := Nat.one_le_two_pow

end FailureBudget

end

end Factoring
end QuantumAlg

end
