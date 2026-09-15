/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.EllipticCurve.P256.DomainParameters
import all QuantumAlg.Algorithms.FiniteCyclicDLP.PrimeOrderTailBound

-- Intentional exception: exact decimal certificates stay on one line for auditability.
set_option linter.style.longLine false

/-!
# P-256 retry calibration

This lightweight module instantiates the prime-order selected-tail bound at the
P-256 subgroup order and the one-percent failure budget. It intentionally has
no dependency on a width-specialized elliptic-curve circuit tree.
-/

section

namespace QuantumAlg

open Factoring
open EllipticCurve.P256.DomainParameters

noncomputable section

namespace FiniteCyclicDLP
namespace PrimeOrderTailBound
namespace P256

/-- Fourier modulus selected by the generic order-finding construction. -/
def fourierModulus : Nat := 2 ^ 260

/-- Public one-percent target failure budget. -/
def failureBudget : FailureBudget where
  failureNumerator := 1
  failureDenominator := 100

/-- Auxiliary failure target that reserves one part in 200,000 for an
exceptional-event analysis. -/
def analysisFailureBudget : FailureBudget where
  failureNumerator := 1999
  failureDenominator := 200000

/-- The auxiliary analysis target is a well-formed rational failure budget. -/
theorem analysisFailureBudget_wellFormed : analysisFailureBudget.WellFormed := by
  constructor <;> norm_num [analysisFailureBudget]

/-- Oversampled exponent-register width derived from the P-256 subgroup order. -/
def exponentRegisterWidth : Nat :=
  Nat.clog 2 (12 * subgroupOrder)

set_option exponentiation.threshold 260 in
/-- The derived exponent-register width is 260 bits. -/
theorem exponentRegisterWidth_eq_260 : exponentRegisterWidth = 260 := by
  change Nat.clog 2 (12 * subgroupOrder) = 260
  have h260 : (260 : Nat) = 13 * 20 := by norm_num
  have h259 : (259 : Nat) = 12 * 20 + 19 := by norm_num
  apply Nat.le_antisymm
  · apply Nat.clog_le_of_le_pow
    rw [h260, pow_mul]
    norm_num [subgroupOrder]
  · have hpower : 2 ^ 259 < 12 * subgroupOrder := by
      rw [h259, pow_add, pow_mul]
      norm_num [subgroupOrder]
    have hclog : 259 < Nat.clog 2 (12 * subgroupOrder) :=
      (Nat.lt_clog_iff_pow_lt (by norm_num)).2 hpower
    exact Nat.succ_le_iff.mpr hclog

/-- The analysis failure target and the exceptional reserve add to the public
one-percent failure target. -/
theorem analysisFailure_plus_exceptionalReserve_eq_publicFailure :
    analysisFailureBudget.value + (1 : Real) / 200000 =
      failureBudget.value := by
  norm_num [analysisFailureBudget, failureBudget, FailureBudget.value]

private def successRatio : Real :=
  ((subgroupOrder * (subgroupOrder - 1) : Nat) : Real) /
    ((4 * fourierModulus ^ 2 -
      subgroupOrder * (subgroupOrder - 1) : Nat) : Real)

private def ratioLower : Real := 9775171 / 10000000000
private def ratioUpper : Real := 9775172 / 10000000000

private theorem fourierModulus_eq : fourierModulus =
    1852673427797059126777135760139006525652319754650249024631321344126610074238976 := by
  unfold fourierModulus
  rw [show (260 : Nat) = 13 * 20 by norm_num, pow_mul]
  norm_num

private theorem successNumerator_eq :
    subgroupOrder * (subgroupOrder - 1) =
      13407807923699100001122556707991011683539144782337215714197757520644865594255592654912056572412765196683019333485218014587891634852103160196180551312563792 := by
  norm_num [subgroupOrder]

private theorem successDenominator_eq :
    4 * fourierModulus ^ 2 =
      13729595320261219429963801598162786434538870600286610818788926918371086366795312104245119281322909109954592622782961716074243975999433287625148056582230114304 := by
  rw [fourierModulus_eq]
  norm_num

private theorem failureNumerator_eq :
    4 * fourierModulus ^ 2 - subgroupOrder * (subgroupOrder - 1) =
      13716187512337520329962679041454795422855331455504273603074729160850441501201056511590207224750496344757909603449476498059656084364581184464951876030917550512 := by
  rw [successDenominator_eq, successNumerator_eq]

private theorem successRatio_lower : ratioLower ≤ successRatio := by
  rw [successRatio, failureNumerator_eq, successNumerator_eq]
  norm_num [ratioLower]

private theorem successRatio_upper : successRatio ≤ ratioUpper := by
  rw [successRatio, failureNumerator_eq, successNumerator_eq]
  norm_num [ratioUpper]

private theorem sourceRatio_eq_one_add_successRatio :
    (((4 * fourierModulus ^ 2 : Nat) : Real) /
        ((4 * fourierModulus ^ 2 -
          subgroupOrder * (subgroupOrder - 1) : Nat) : Real)) =
      1 + successRatio := by
  rw [failureNumerator_eq, successDenominator_eq]
  unfold successRatio
  rw [failureNumerator_eq, successNumerator_eq]
  norm_num

private theorem log_one_add_successRatio_bounds :
    ratioLower - ratioUpper ^ 2 / 2 -
        ratioUpper ^ 3 / (3 * (1 - ratioUpper)) ≤
      Real.log (1 + successRatio) ∧
    Real.log (1 + successRatio) ≤
      ratioUpper - ratioLower ^ 2 / 2 +
        ratioUpper ^ 3 / (3 * (1 - ratioUpper)) := by
  have haNonneg : 0 ≤ ratioLower := by norm_num [ratioLower]
  have hbNonneg : 0 ≤ ratioUpper := by norm_num [ratioUpper]
  have hbLtOne : ratioUpper < 1 := by norm_num [ratioUpper]
  have hxNonneg : 0 ≤ successRatio :=
    haNonneg.trans successRatio_lower
  have hxLtOne : successRatio < 1 :=
    successRatio_upper.trans_lt hbLtOne
  have hxCube : successRatio ^ 3 ≤ ratioUpper ^ 3 :=
    pow_le_pow_left₀ hxNonneg successRatio_upper 3
  have hxSquareUpper : successRatio ^ 2 ≤ ratioUpper ^ 2 :=
    pow_le_pow_left₀ hxNonneg successRatio_upper 2
  have hxSquareLower : ratioLower ^ 2 ≤ successRatio ^ 2 :=
    pow_le_pow_left₀ haNonneg successRatio_lower 2
  have herror :
      successRatio ^ 3 / (3 * (1 - successRatio)) ≤
        ratioUpper ^ 3 / (3 * (1 - ratioUpper)) := by
    have hxDenom : 0 < 3 * (1 - successRatio) := by positivity
    have hbDenom : 0 < 3 * (1 - ratioUpper) := by positivity
    apply (div_le_div_iff₀ hxDenom hbDenom).2
    calc
      successRatio ^ 3 * (3 * (1 - ratioUpper)) ≤
          ratioUpper ^ 3 * (3 * (1 - ratioUpper)) :=
        mul_le_mul_of_nonneg_right hxCube hbDenom.le
      _ ≤ ratioUpper ^ 3 * (3 * (1 - successRatio)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hbNonneg 3)
        nlinarith [successRatio_upper]
  have htaylor := abs_log_one_add_sub_quadratic_le hxNonneg hxLtOne
  rw [abs_le] at htaylor
  have hlogLower :
      successRatio - successRatio ^ 2 / 2 -
          successRatio ^ 3 / (3 * (1 - successRatio)) ≤
        Real.log (1 + successRatio) := by
    linarith [htaylor.1]
  have hlogUpper :
      Real.log (1 + successRatio) ≤
        successRatio - successRatio ^ 2 / 2 +
          successRatio ^ 3 / (3 * (1 - successRatio)) := by
    linarith [htaylor.2]
  constructor
  · apply le_trans _ hlogLower
    linarith [successRatio_lower, hxSquareUpper, herror]
  · apply hlogUpper.trans
    linarith [successRatio_upper, hxSquareLower, herror]

private theorem sourceLog_pos :
    0 < Real.log
      (((4 * fourierModulus ^ 2 : Nat) : Real) /
        ((4 * fourierModulus ^ 2 -
          subgroupOrder * (subgroupOrder - 1) : Nat) : Real)) := by
  rw [sourceRatio_eq_one_add_successRatio]
  apply Real.log_pos
  have hxPos : 0 < successRatio :=
    lt_of_lt_of_le (by norm_num [ratioLower]) successRatio_lower
  linarith

/-- The shared prime-order tail bound calibrates the one-percent P-256
instantiation to exactly 4,714 repetitions. -/
theorem retryCount_eq_4714 :
    retryCount subgroupOrder fourierModulus failureBudget = 4714 := by
  have hlogBounds := log_one_add_successRatio_bounds
  have hlogFloor := hlogBounds.1
  have hlogCeiling := hlogBounds.2
  have hlogHundred :
      Real.log (100 : Real) =
        2 * (Real.log 2 + Real.log 5) := by
    calc
      Real.log (100 : Real) = Real.log ((2 * 5 : Real) ^ 2) := by norm_num
      _ = 2 * Real.log (2 * 5 : Real) := by
        rw [Real.log_pow]
        norm_num
      _ = 2 * (Real.log 2 + Real.log 5) := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
  have hlogHundredLower :
      (46051701852 : Real) / 10000000000 < Real.log 100 := by
    rw [hlogHundred]
    nlinarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hlogHundredUpper :
      Real.log 100 < (46051701868 : Real) / 10000000000 := by
    rw [hlogHundred]
    nlinarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hnumericLower :
      (4713 : Real) *
          (ratioUpper - ratioLower ^ 2 / 2 +
            ratioUpper ^ 3 / (3 * (1 - ratioUpper))) <
        (46051701852 : Real) / 10000000000 := by
    norm_num [ratioLower, ratioUpper]
  have hnumericUpper :
      (46051701868 : Real) / 10000000000 ≤
        (4714 : Real) *
          (ratioLower - ratioUpper ^ 2 / 2 -
            ratioUpper ^ 3 / (3 * (1 - ratioUpper))) := by
    norm_num [ratioLower, ratioUpper]
  have hsourceLog := sourceLog_pos
  have hlower :
      (4713 : Real) *
          Real.log
            (((4 * fourierModulus ^ 2 : Nat) : Real) /
              ((4 * fourierModulus ^ 2 -
                subgroupOrder * (subgroupOrder - 1) : Nat) : Real)) <
        Real.log 100 := by
    rw [sourceRatio_eq_one_add_successRatio]
    calc
      (4713 : Real) * Real.log (1 + successRatio) ≤
          4713 *
            (ratioUpper - ratioLower ^ 2 / 2 +
              ratioUpper ^ 3 / (3 * (1 - ratioUpper))) :=
        mul_le_mul_of_nonneg_left hlogCeiling (by norm_num)
      _ < (46051701852 : Real) / 10000000000 := hnumericLower
      _ < Real.log 100 := hlogHundredLower
  have hupper :
      Real.log 100 ≤
        (4714 : Real) *
          Real.log
            (((4 * fourierModulus ^ 2 : Nat) : Real) /
              ((4 * fourierModulus ^ 2 -
                subgroupOrder * (subgroupOrder - 1) : Nat) : Real)) := by
    rw [sourceRatio_eq_one_add_successRatio]
    calc
      Real.log 100 ≤ (46051701868 : Real) / 10000000000 :=
        hlogHundredUpper.le
      _ ≤ 4714 *
          (ratioLower - ratioUpper ^ 2 / 2 -
            ratioUpper ^ 3 / (3 * (1 - ratioUpper))) := hnumericUpper
      _ ≤ 4714 * Real.log (1 + successRatio) :=
        mul_le_mul_of_nonneg_left hlogFloor (by norm_num)
  apply retryCount_eq_of_log_bounds failureBudget (by norm_num) hsourceLog
  · simpa [failureBudget] using hlower
  · simpa [failureBudget] using hupper

/-- The auxiliary analysis target retains the calibrated 4,714 repetitions. -/
theorem analysisRetryCount_eq_4714 :
    retryCount subgroupOrder fourierModulus analysisFailureBudget = 4714 := by
  have hlogBounds := log_one_add_successRatio_bounds
  have hlogFloor := hlogBounds.1
  have hlogHundred :
      Real.log (100 : Real) =
        2 * (Real.log 2 + Real.log 5) := by
    calc
      Real.log (100 : Real) = Real.log ((2 * 5 : Real) ^ 2) := by norm_num
      _ = 2 * Real.log (2 * 5 : Real) := by
        rw [Real.log_pow]
        norm_num
      _ = 2 * (Real.log 2 + Real.log 5) := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
  have hlogHundredUpper :
      Real.log 100 < (46051701868 : Real) / 10000000000 := by
    rw [hlogHundred]
    nlinarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hlogAdjustment :
      Real.log ((2000 : Real) / 1999) ≤ (1 : Real) / 1999 := by
    calc
      Real.log ((2000 : Real) / 1999) ≤ (2000 : Real) / 1999 - 1 :=
        Real.log_le_sub_one_of_pos (by norm_num)
      _ = (1 : Real) / 1999 := by norm_num
  have htargetUpper :
      Real.log
          ((analysisFailureBudget.failureDenominator : Real) /
            analysisFailureBudget.failureNumerator) ≤
        (4714 : Real) *
          Real.log
            (((4 * fourierModulus ^ 2 : Nat) : Real) /
              ((4 * fourierModulus ^ 2 -
                subgroupOrder * (subgroupOrder - 1) : Nat) : Real)) := by
    calc
      Real.log
          ((analysisFailureBudget.failureDenominator : Real) /
            analysisFailureBudget.failureNumerator) =
          Real.log 100 + Real.log ((2000 : Real) / 1999) := by
        change Real.log ((200000 : Real) / 1999) = _
        rw [show ((200000 : Real) / 1999) =
          100 * ((2000 : Real) / 1999) by norm_num]
        rw [Real.log_mul (by norm_num) (by norm_num)]
      _ ≤ (46051701868 : Real) / 10000000000 + (1 : Real) / 1999 :=
        add_le_add hlogHundredUpper.le hlogAdjustment
      _ ≤ 4714 *
          (ratioLower - ratioUpper ^ 2 / 2 -
            ratioUpper ^ 3 / (3 * (1 - ratioUpper))) := by
        norm_num [ratioLower, ratioUpper]
      _ ≤ 4714 * Real.log (1 + successRatio) :=
        mul_le_mul_of_nonneg_left hlogFloor (by norm_num)
      _ = 4714 *
          Real.log
            (((4 * fourierModulus ^ 2 : Nat) : Real) /
              ((4 * fourierModulus ^ 2 -
                subgroupOrder * (subgroupOrder - 1) : Nat) : Real)) := by
        rw [sourceRatio_eq_one_add_successRatio]
  have hsourceLog := sourceLog_pos
  have hcountUpper :
      retryCount subgroupOrder fourierModulus analysisFailureBudget ≤ 4714 := by
    rw [retryCount_eq_closedForm]
    apply max_le
    · norm_num
    · apply Nat.ceil_le.mpr
      exact (div_le_iff₀ hsourceLog).2 htargetUpper
  have htargetMonotone :
      Real.log
          ((failureBudget.failureDenominator : Real) /
            failureBudget.failureNumerator) ≤
        Real.log
          ((analysisFailureBudget.failureDenominator : Real) /
            analysisFailureBudget.failureNumerator) := by
    simpa [failureBudget, analysisFailureBudget] using
      (Real.log_le_log (by norm_num : (0 : Real) < 100)
        (by norm_num : (100 : Real) ≤ (200000 : Real) / 1999))
  have hExponentMonotone :
      Real.log
          ((failureBudget.failureDenominator : Real) /
            failureBudget.failureNumerator) /
          Real.log
            (((4 * fourierModulus ^ 2 : Nat) : Real) /
              ((4 * fourierModulus ^ 2 -
                subgroupOrder * (subgroupOrder - 1) : Nat) : Real)) ≤
        Real.log
          ((analysisFailureBudget.failureDenominator : Real) /
            analysisFailureBudget.failureNumerator) /
          Real.log
            (((4 * fourierModulus ^ 2 : Nat) : Real) /
              ((4 * fourierModulus ^ 2 -
                subgroupOrder * (subgroupOrder - 1) : Nat) : Real)) :=
    (div_le_div_iff_of_pos_right hsourceLog).2 htargetMonotone
  have hcountLower :
      retryCount subgroupOrder fourierModulus failureBudget ≤
        retryCount subgroupOrder fourierModulus analysisFailureBudget := by
    simp only [retryCount_eq_closedForm]
    exact max_le_max_left 1 (Nat.ceil_mono hExponentMonotone)
  have hcountLower4714 :
      4714 ≤ retryCount subgroupOrder fourierModulus analysisFailureBudget := by
    rw [← retryCount_eq_4714]
    exact hcountLower
  exact Nat.le_antisymm hcountUpper hcountLower4714

end P256
end PrimeOrderTailBound
end FiniteCyclicDLP

end

end QuantumAlg

end
