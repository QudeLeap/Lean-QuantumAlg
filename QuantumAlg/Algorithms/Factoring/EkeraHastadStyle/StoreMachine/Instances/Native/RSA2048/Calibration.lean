/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Count

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration

/-!
# Exact seven-batch calibration at the RSA-2048 width

The original width-specific formulas place the one-time key exception outside
the seventh power of the conditional batch failure. Their sum is strictly less
than one percent. The fixed seven batches use this tighter calculation; they
are separate from the generic retry count based on the `147 / 256` ceiling.
These are pure numerical bounds, independent of an executable or output law.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRSA2048.Calibration

noncomputable section

/-- The one-time RSA-2048 key exception plus seven conditional batch failures
is strictly below one percent. -/
lemma keygenFailure_seven_lt_onePercent :
    ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound 1024) +
        NativeFiniteRetry.Calibration.batchFailure 1024 ^ 7 <
      ENNReal.ofReal ((1 : Real) / 100) := by
  have effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ 1024 := by
    norm_num [RSA.GeneratorOrder.effectiveCutoffBits]
  have failureNonneg :
      0 ≤ 1 -
        (1 - RSA.FixedWidthSampling.samplerFailureBound 1024) *
          (BinomialTail.sixteenSampleBatchFloor : Real) := by
    rw [RSA.FixedWidthSampling.samplerFailureBound,
      RSA.GeneratorOrder.generatorFailureBound]
    norm_num [BinomialTail.sixteenSampleBatchFloor,
      BinomialTail.atLeastTwoOfSixteenAtOneEighth]
  rw [NativeFiniteRetry.Calibration.batchFailure_eq_ofReal_of_effective effective,
    ← ENNReal.ofReal_pow failureNonneg 7,
    ← ENNReal.ofReal_add (RSA.GeneratorOrder.keyFailureBound_nonneg 1024)
      (pow_nonneg failureNonneg 7)]
  rw [RSA.GeneratorOrder.keyFailureBound,
    RSA.FixedWidthSampling.samplerFailureBound,
    RSA.GeneratorOrder.generatorFailureBound,
    RSA.GeneratorOrder.rsa1024_loss_thresholds.2.2]
  rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : Real) < 1 / 100)]
  norm_num [BinomialTail.sixteenSampleBatchFloor,
    BinomialTail.atLeastTwoOfSixteenAtOneEighth]

/-- The conditional seven-batch failure term alone is strictly below one
percent at the RSA-2048 width. -/
lemma batchFailure_seven_lt_onePercent :
    NativeFiniteRetry.Calibration.batchFailure 1024 ^ 7 <
      ENNReal.ofReal ((1 : Real) / 100) := by
  have addBound :
      NativeFiniteRetry.Calibration.batchFailure 1024 ^ 7 ≤
        ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound 1024) +
          NativeFiniteRetry.Calibration.batchFailure 1024 ^ 7 := by
    calc
      NativeFiniteRetry.Calibration.batchFailure 1024 ^ 7 =
          0 + NativeFiniteRetry.Calibration.batchFailure 1024 ^ 7 :=
        (zero_add _).symm
      _ ≤ ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound 1024) +
            NativeFiniteRetry.Calibration.batchFailure 1024 ^ 7 :=
        add_le_add_left
          (bot_le : 0 ≤ ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound 1024)) _
  exact addBound.trans_lt keygenFailure_seven_lt_onePercent

/-- The complement of conditional seven-batch failure is at least `99 / 100`.
No key-generation exceptional mass is charged to this conditional bound. -/
lemma conditionalSuccess_seven_ge_99 :
    ENNReal.ofReal ((99 : Real) / 100) ≤
      1 - NativeFiniteRetry.Calibration.batchFailure 1024 ^ 7 := by
  rw [show (99 : Real) / 100 = 1 - 1 / 100 by norm_num,
    ENNReal.ofReal_sub 1 (by norm_num : (0 : Real) ≤ 1 / 100),
    ENNReal.ofReal_one]
  exact tsub_le_tsub_left batchFailure_seven_lt_onePercent.le 1

/-- The complement of the combined one-time key exception and seven-batch
conditional failure is at least `99 / 100`. -/
lemma combinedSuccess_seven_ge_99 :
    ENNReal.ofReal ((99 : Real) / 100) ≤
      1 - (ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound 1024) +
        NativeFiniteRetry.Calibration.batchFailure 1024 ^ 7) := by
  rw [show (99 : Real) / 100 = 1 - 1 / 100 by norm_num,
    ENNReal.ofReal_sub 1 (by norm_num : (0 : Real) ≤ 1 / 100),
    ENNReal.ofReal_one]
  exact tsub_le_tsub_left keygenFailure_seven_lt_onePercent.le 1

/-- Conditional failure of a twenty-member RSA-2048 batch, retaining the
exact 190-pair obstruction union cost. -/
def twentyBatchFailure : ENNReal :=
  ENNReal.ofReal (1 -
    (1 - RSA.FixedWidthSampling.samplerFailureBound 1024) *
      (BinomialTail.twentySampleBatchFloor : Real))

/-- The calibrated failure scalar is the complement of the proved twenty-member floor. -/
lemma twentyBatchFailure_eq_one_sub_successFloor :
    twentyBatchFailure = 1 - NativeBatchSuccess.twentySuccessFloor 1024 := by
  have samplerNonneg : 0 ≤ RSA.FixedWidthSampling.samplerFailureBound 1024 := by
    rw [RSA.FixedWidthSampling.samplerFailureBound,
      RSA.GeneratorOrder.generatorFailureBound]
    norm_num
  have samplerLe : RSA.FixedWidthSampling.samplerFailureBound 1024 ≤ 1 := by
    rw [RSA.FixedWidthSampling.samplerFailureBound,
      RSA.GeneratorOrder.generatorFailureBound]
    norm_num
  have floorNonneg : 0 ≤ (BinomialTail.twentySampleBatchFloor : Real) := by
    norm_num [BinomialTail.twentySampleBatchFloor,
      BinomialTail.atLeastTwoOfTwentyAtOneEighth]
  unfold twentyBatchFailure NativeBatchSuccess.twentySuccessFloor
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 samplerNonneg,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr samplerLe),
    ← ENNReal.ofReal_sub 1 (mul_nonneg (sub_nonneg.mpr samplerLe) floorNonneg)]

/-- The original ordered-key exceptional mass is charged once, outside all
four independent conditional batch failures. -/
lemma keygenFailure_twentyByFour_lt_onePercent :
    ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound 1024) +
        twentyBatchFailure ^ 4 < ENNReal.ofReal ((1 : Real) / 100) := by
  have failureNonneg : 0 ≤ 1 -
      (1 - RSA.FixedWidthSampling.samplerFailureBound 1024) *
        (BinomialTail.twentySampleBatchFloor : Real) := by
    rw [RSA.FixedWidthSampling.samplerFailureBound,
      RSA.GeneratorOrder.generatorFailureBound]
    norm_num [BinomialTail.twentySampleBatchFloor,
      BinomialTail.atLeastTwoOfTwentyAtOneEighth]
  rw [twentyBatchFailure, ← ENNReal.ofReal_pow failureNonneg 4,
    ← ENNReal.ofReal_add (RSA.GeneratorOrder.keyFailureBound_nonneg 1024)
      (pow_nonneg failureNonneg 4)]
  rw [RSA.GeneratorOrder.keyFailureBound,
    RSA.FixedWidthSampling.samplerFailureBound,
    RSA.GeneratorOrder.generatorFailureBound,
    RSA.GeneratorOrder.rsa1024_loss_thresholds.2.2]
  rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : Real) < 1 / 100)]
  norm_num [BinomialTail.twentySampleBatchFloor,
    BinomialTail.atLeastTwoOfTwentyAtOneEighth]

/-- The combined key and four-batch failure leaves success at least 99 percent. -/
lemma combinedSuccess_twentyByFour_ge_99 :
    ENNReal.ofReal ((99 : Real) / 100) ≤
      1 - (ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound 1024) +
        twentyBatchFailure ^ 4) := by
  rw [show (99 : Real) / 100 = 1 - 1 / 100 by norm_num,
    ENNReal.ofReal_sub 1 (by norm_num : (0 : Real) ≤ 1 / 100),
    ENNReal.ofReal_one]
  exact tsub_le_tsub_left keygenFailure_twentyByFour_lt_onePercent.le 1

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRSA2048.Calibration
