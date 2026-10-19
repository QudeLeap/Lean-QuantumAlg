/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.Common
public import QuantumAlg.Util.RSA.GeneratorOrder
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

import all QuantumAlg.Algorithms.Factoring.Common
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Specification

/-!
# Shared real calibration for actual finite batch repetition

An arbitrary real failure target selects the natural ceiling of
log(eta / 2) / log(147 / 256). The original batch failure floor is unchanged.
Conditional retry loss receives half the target; original-key loss is charged
once outside the retry power. Both generic native RSA and declared EH use
this single calibration. The fixed RSA-2048 instance retains its separate,
tighter seven-batch bound; the generic one-percent count is ten.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry.Calibration

noncomputable section

/-- Conditional one-batch failure ceiling induced by the canonical success
floor. -/
public def batchFailure (bitWidth : Nat) : ENNReal :=
  1 - NativeBatchSuccess.successFloor bitWidth

/-- Exact real normalization of the canonical conditional batch failure in
the effective-width range. -/
lemma batchFailure_eq_ofReal_of_effective {bitWidth : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth) :
    batchFailure bitWidth =
      ENNReal.ofReal
        (1 - ((1 - RSA.FixedWidthSampling.samplerFailureBound bitWidth) *
          (BinomialTail.sixteenSampleBatchFloor : Real))) := by
  have failureNonneg :
      0 ≤ RSA.FixedWidthSampling.samplerFailureBound bitWidth := by
    unfold RSA.FixedWidthSampling.samplerFailureBound
      RSA.GeneratorOrder.generatorFailureBound
    positivity
  have failureLeOne :
      RSA.FixedWidthSampling.samplerFailureBound bitWidth ≤ 1 := by
    exact (RSA.FixedWidthSampling.samplerFailureBound_le_effective
      effective).trans (by norm_num)
  have complementNonneg :
      0 ≤ 1 - RSA.FixedWidthSampling.samplerFailureBound bitWidth :=
    sub_nonneg.mpr failureLeOne
  have productNonneg :
      0 ≤ (1 - RSA.FixedWidthSampling.samplerFailureBound bitWidth) *
        (BinomialTail.sixteenSampleBatchFloor : Real) := by
    exact mul_nonneg complementNonneg (by
      norm_num [BinomialTail.sixteenSampleBatchFloor,
        BinomialTail.atLeastTwoOfSixteenAtOneEighth])
  unfold batchFailure NativeBatchSuccess.successFloor
  rw [← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 failureNonneg,
    ← ENNReal.ofReal_mul complementNonneg,
    ← ENNReal.ofReal_sub 1 productNonneg]

/-- At every effective RSA width, the canonical shared-batch success floor is
at least `109 / 256`. -/
lemma oneHundredNineOver256_le_successFloor {bitWidth : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth) :
    ENNReal.ofReal ((109 : Real) / 256) ≤ NativeBatchSuccess.successFloor bitWidth := by
  let bound : Real := (513 / 1024 : Real) ^ 16 + 1 / 8
  have boundNonneg : 0 ≤ bound := by
    dsimp [bound]
    positivity
  have boundLeOne : bound ≤ 1 := by
    dsimp [bound]
    norm_num
  have samplerBound :
      RSA.FixedWidthSampling.samplerFailureBound bitWidth ≤ bound := by
    exact RSA.FixedWidthSampling.samplerFailureBound_le_effective effective
  have failureBound :
      ENNReal.ofReal
          (RSA.FixedWidthSampling.samplerFailureBound bitWidth) ≤
        ENNReal.ofReal bound := by
    exact ENNReal.ofReal_le_ofReal samplerBound
  calc
    ENNReal.ofReal ((109 : Real) / 256) ≤
        ENNReal.ofReal
          ((1 - bound) * BinomialTail.sixteenSampleBatchFloor) := by
      apply ENNReal.ofReal_le_ofReal
      dsimp [bound]
      norm_num [BinomialTail.sixteenSampleBatchFloor,
        BinomialTail.atLeastTwoOfSixteenAtOneEighth]
    _ = (1 - ENNReal.ofReal bound) *
          ENNReal.ofReal (BinomialTail.sixteenSampleBatchFloor : Real) := by
      rw [ENNReal.ofReal_mul (sub_nonneg.mpr boundLeOne),
        ENNReal.ofReal_sub 1 boundNonneg, ENNReal.ofReal_one]
    _ ≤ (1 - ENNReal.ofReal
          (RSA.FixedWidthSampling.samplerFailureBound bitWidth)) *
          ENNReal.ofReal (BinomialTail.sixteenSampleBatchFloor : Real) := by
      simpa [mul_comm] using mul_le_mul_right
        (tsub_le_tsub_left failureBound 1)
        (ENNReal.ofReal (BinomialTail.sixteenSampleBatchFloor : Real))
    _ = NativeBatchSuccess.successFloor bitWidth := rfl

/-- Conditional canonical batch failure is at most `147 / 256` throughout
the effective range. -/
lemma batchFailure_le_147Over256 {bitWidth : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth) :
    batchFailure bitWidth ≤ ENNReal.ofReal ((147 : Real) / 256) := by
  rw [show (147 : Real) / 256 = 1 - 109 / 256 by norm_num,
    ENNReal.ofReal_sub 1 (by norm_num : (0 : Real) ≤ 109 / 256),
    ENNReal.ofReal_one]
  exact tsub_le_tsub_left
    (oneHundredNineOver256_le_successFloor effective) 1

/-- The real exponent in the agreed direct failure-ratio formula. -/
public def realRetryExponent (η : Real) : Real :=
  Real.log (η / 2) / Real.log ((147 : Real) / 256)

/-- The least natural ceiling of the real exponent, without a redundant maximum. -/
public def retryCount (η : Real) : Nat :=
  Nat.ceil (realRetryExponent η)

/-- The direct and reciprocal logarithm formulas agree, even at totalized zero. -/
public lemma realRetryExponent_eq_inverse_log (η : Real) :
    realRetryExponent η = Real.log (2 / η) / Real.log ((256 : Real) / 147) := by
  have numerator : Real.log (η / 2) = -Real.log (2 / η) := by
    rw [show η / 2 = (2 / η)⁻¹ by rw [inv_div], Real.log_inv]
  have denominator :
      Real.log ((147 : Real) / 256) = -Real.log ((256 : Real) / 147) := by
    rw [show (147 : Real) / 256 = ((256 : Real) / 147)⁻¹ by norm_num,
      Real.log_inv]
  rw [realRetryExponent, numerator, denominator, neg_div_neg_eq]

/-- The retry count can equivalently be read using positive reciprocal logarithms. -/
public lemma realRetryCount_eq_inverse_log (η : Real) :
    retryCount η = Nat.ceil (Real.log (2 / η) / Real.log ((256 : Real) / 147)) := by
  rw [retryCount, realRetryExponent_eq_inverse_log]

/-- An admissible failure target gives a strictly positive real exponent. -/
public lemma realRetryExponent_pos (η : Real) (positive : 0 < η) (lessOne : η < 1) :
    0 < realRetryExponent η := by
  have ratioGreater : 1 < (2 : Real) / η := by
    apply (lt_div_iff₀ positive).mpr
    linarith
  rw [realRetryExponent_eq_inverse_log]
  exact div_pos (Real.log_pos ratioGreater) (Real.log_pos (by norm_num))

/-- An admissible failure target requires at least one batch. -/
public lemma realRetryCount_pos (η : Real) (positive : 0 < η) (lessOne : η < 1) :
    0 < retryCount η := by
  exact Nat.ceil_pos.mpr (realRetryExponent_pos η positive lessOne)

/-- On the admissible domain the older maximum-with-one form adds nothing. -/
public lemma realRetryCount_eq_max_inverse_log (η : Real)
    (positive : 0 < η) (lessOne : η < 1) :
    retryCount η = max 1
      (Nat.ceil (Real.log (2 / η) / Real.log ((256 : Real) / 147))) := by
  have oneLe : 1 ≤ retryCount η := realRetryCount_pos η positive lessOne
  rw [← realRetryCount_eq_inverse_log, max_eq_right oneLe]

/-- The selected number of batches bounds the generic failure by half the target. -/
public lemma realRetryFailure_power_le_half (η : Real) (positive : 0 < η) :
    ((147 : Real) / 256) ^ retryCount η ≤ η / 2 := by
  let ratio : Real := 256 / 147
  have ratioPositive : 0 < ratio := by norm_num [ratio]
  have ratioGreater : 1 < ratio := by norm_num [ratio]
  have logPositive : 0 < Real.log ratio := Real.log_pos ratioGreater
  have exponentLe : Real.log (2 / η) / Real.log ratio ≤ (retryCount η : Real) := by
    rw [realRetryCount_eq_inverse_log]
    exact Nat.le_ceil _
  have logLe : Real.log (2 / η) ≤ (retryCount η : Real) * Real.log ratio :=
    (div_le_iff₀ logPositive).mp exponentLe
  have ratioLe : 2 / η ≤ ratio ^ retryCount η := by
    calc
      2 / η = Real.exp (Real.log (2 / η)) :=
        (Real.exp_log (div_pos (by norm_num) positive)).symm
      _ ≤ Real.exp ((retryCount η : Real) * Real.log ratio) :=
        Real.exp_le_exp.mpr logLe
      _ = ratio ^ retryCount η := by
        rw [← Real.log_pow]
        exact Real.exp_log (pow_pos ratioPositive _)
  have multiplied : 2 ≤ ratio ^ retryCount η * η :=
    (div_le_iff₀ positive).mp ratioLe
  have cancel : ratio ^ retryCount η * ((147 : Real) / 256) ^ retryCount η = 1 := by
    rw [← mul_pow]
    norm_num [ratio]
  have twiceLe : 2 * ((147 : Real) / 256) ^ retryCount η ≤ η := by
    calc
      2 * ((147 : Real) / 256) ^ retryCount η ≤
          (ratio ^ retryCount η * η) * ((147 : Real) / 256) ^ retryCount η :=
        mul_le_mul_of_nonneg_right multiplied (by positivity)
      _ = η * (ratio ^ retryCount η * ((147 : Real) / 256) ^ retryCount η) := by ring
      _ = η := by rw [cancel, mul_one]
  linarith

/-- Nine reciprocal powers fall strictly below the one-percent threshold. -/
public lemma realRetryInversePower_nine_lt_twoHundred :
    ((256 : Real) / 147) ^ 9 < 200 := by
  norm_num

/-- Ten reciprocal powers reach the one-percent threshold. -/
public lemma realRetryInversePower_twoHundred_le_ten :
    (200 : Real) ≤ ((256 : Real) / 147) ^ 10 := by
  norm_num

/-- The generic real calibration selects exactly ten batches at a one-percent target. -/
public lemma realRetryCount_one_percent : retryCount ((1 : Real) / 100) = 10 := by
  have ratioPositive : 0 < (256 : Real) / 147 := by norm_num
  have logPositive : 0 < Real.log ((256 : Real) / 147) :=
    Real.log_pos (by norm_num)
  have lowerLog : (9 : Real) * Real.log ((256 : Real) / 147) < Real.log 200 := by
    have result := Real.log_lt_log (pow_pos ratioPositive 9)
      realRetryInversePower_nine_lt_twoHundred
    simpa only [Real.log_pow, Nat.cast_ofNat] using result
  have upperLog : Real.log 200 ≤ (10 : Real) * Real.log ((256 : Real) / 147) := by
    have result := Real.log_le_log (by norm_num : (0 : Real) < 200)
      realRetryInversePower_twoHundred_le_ten
    simpa only [Real.log_pow, Nat.cast_ofNat] using result
  have lower : (9 : Real) < Real.log 200 / Real.log ((256 : Real) / 147) :=
    (lt_div_iff₀ logPositive).mpr lowerLog
  have upper : Real.log 200 / Real.log ((256 : Real) / 147) ≤ (10 : Real) :=
    (div_le_iff₀ logPositive).mpr upperLog
  have evaluated :
      realRetryExponent ((1 : Real) / 100) = Real.log 200 / Real.log ((256 : Real) / 147) := by
    rw [realRetryExponent_eq_inverse_log]
    norm_num
  rw [retryCount, evaluated]
  exact Nat.le_antisymm (Nat.ceil_le.mpr upper) (Nat.succ_le_of_lt (Nat.lt_ceil.mpr lower))

/-- Any certified conditional failure below the generic ceiling has the half-target power. -/
public lemma realFailureCalibration_ennrealPower_le_half
    (η : Real) (positive : 0 < η) (failure : ENNReal)
    (bounded : failure ≤ ENNReal.ofReal ((147 : Real) / 256)) :
    failure ^ retryCount η ≤ ENNReal.ofReal (η / 2) := by
  calc
    failure ^ retryCount η ≤
        ENNReal.ofReal ((147 : Real) / 256) ^ retryCount η :=
      pow_le_pow_left' bounded _
    _ ≤ ENNReal.ofReal (η / 2) := by
      rw [← ENNReal.ofReal_pow (by norm_num : (0 : Real) ≤ 147 / 256)]
      exact ENNReal.ofReal_le_ofReal
        (realRetryFailure_power_le_half η positive)

/-- The exact real conditional-success threshold agrees with ENNReal subtraction. -/
public lemma realFailureCalibration_halfSuccess_eq
    (η : Real) (positive : 0 < η) :
    ENNReal.ofReal (1 - η / 2) = 1 - ENNReal.ofReal (η / 2) := by
  rw [ENNReal.ofReal_sub 1 (by positivity : (0 : Real) ≤ η / 2), ENNReal.ofReal_one]

/-- An existing same-run success theorem receives the numerical half-target without new PMFs. -/
public lemma realFailureCalibration_conditionalSuccess
    (η : Real) (positive : 0 < η) (failure success : ENNReal)
    (bounded : failure ≤ ENNReal.ofReal ((147 : Real) / 256))
    (actual : 1 - failure ^ retryCount η ≤ success) :
    1 - ENNReal.ofReal (η / 2) ≤ success :=
  (tsub_le_tsub_left
    (realFailureCalibration_ennrealPower_le_half η positive failure bounded) 1).trans actual

/-- Key loss is charged once, outside the conditional retry power. -/
public lemma realFailureCalibration_twoHalvesSuccess
    (η : Real) (positive : 0 < η) (keyLoss retryLoss success : ENNReal)
    (keyBound : keyLoss ≤ ENNReal.ofReal (η / 2))
    (retryBound : retryLoss ≤ ENNReal.ofReal (η / 2))
    (actual : 1 - (keyLoss + retryLoss) ≤ success) :
    ENNReal.ofReal (1 - η) ≤ success := by
  apply le_trans _ actual
  rw [ENNReal.ofReal_sub 1 positive.le, ENNReal.ofReal_one]
  apply tsub_le_tsub_left
  calc
    keyLoss + retryLoss ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
      add_le_add keyBound retryBound
    _ = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add (by positivity : (0 : Real) ≤ η / 2)
        (by positivity : (0 : Real) ≤ η / 2)]
      congr 1
      ring

/-- The existing batch model plugs into the real scalar theorem at every effective width. -/
public lemma retryBatchFailure_le_halfTarget
    {bitWidth : Nat}
    (effective : QuantumAlg.RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth)
    (η : Real) (positive : 0 < η) :
    batchFailure bitWidth ^
        retryCount η ≤ ENNReal.ofReal (η / 2) :=
  realFailureCalibration_ennrealPower_le_half η positive _
    (batchFailure_le_147Over256 effective)

/-- Compatibility is one-way mathematical specialization, not rationalization of real inputs. -/
public lemma realRetryCount_eq_rationalCalibration
    (budget : FailureBudget) (wellFormed : budget.WellFormed)
    (lessOne : budget.value < 1) :
    retryCount budget.value =
      max 1 (Nat.ceil
        (Real.log (((2 * budget.failureDenominator : Nat) : Real) / budget.failureNumerator) /
          Real.log ((256 : Real) / 147))) := by
  have numeratorNonzero : (budget.failureNumerator : Real) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt wellFormed.numerator_pos)
  have denominatorNonzero : (budget.failureDenominator : Real) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt wellFormed.denominator_pos)
  have reciprocal : 2 / budget.value =
      (((2 * budget.failureDenominator : Nat) : Real) / budget.failureNumerator) := by
    unfold FailureBudget.value
    push_cast
    field_simp [numeratorNonzero, denominatorNonzero]
  simpa only [reciprocal] using
    realRetryCount_eq_max_inverse_log budget.value
      (FailureBudget.value_pos budget wellFormed) lessOne

/-- The public expanded formula is exactly the original private rational count. -/
private lemma realRetryCount_eq_legacy_rationalCalibration
    (budget : FailureBudget) (wellFormed : budget.WellFormed)
    (lessOne : budget.value < 1) :
    retryCount budget.value =
      FailureBudget.retryCountFor
        { failureNumerator := 147, failureDenominator := 256 }
        { failureNumerator := budget.failureNumerator,
          failureDenominator := 2 * budget.failureDenominator } := by
  exact realRetryCount_eq_rationalCalibration budget wellFormed lessOne

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry.Calibration
