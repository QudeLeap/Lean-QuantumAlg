/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.Common

import all QuantumAlg.Algorithms.Factoring.Common
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Specification

/-!
# Original rational calibration for actual finite batch repetition

The conditional batch floor determines its failure complement. The original
conservative rational ceiling and halved target select an exact total count
through the shared failure-budget formula. These are independent mathematical
budgets; their use by an actual run is a separate probability theorem.
The tighter fixed-seven RSA instance remains a separate width-specific result.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry.Calibration

noncomputable section

/-- Conditional one-batch failure ceiling induced by the canonical success
floor. -/
public def batchFailure (bitWidth : Nat) : ENNReal :=
  1 - NativeBatchSuccess.successFloor bitWidth

/-- Exact real normalization of the canonical conditional batch failure in
the effective-width range. -/
theorem batchFailure_eq_ofReal_of_effective {bitWidth : Nat}
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

/-- Conservative rational ceiling for the conditional failure of one
canonical batch. -/
def conditionalFailureBudget : FailureBudget where
  failureNumerator := 147
  failureDenominator := 256

/-- Half of the caller's target is reserved for independent retry failure. -/
def retryTargetBudget (budget : FailureBudget) : FailureBudget where
  failureNumerator := budget.failureNumerator
  failureDenominator := 2 * budget.failureDenominator

/-- Exact retry count calibrated from the canonical one-batch failure
ceiling. -/
public def retryCount (budget : FailureBudget) : Nat :=
  FailureBudget.retryCountFor conditionalFailureBudget
    (retryTargetBudget budget)

/-- At every effective RSA width, the canonical shared-batch success floor is
at least `109 / 256`. -/
theorem oneHundredNineOver256_le_successFloor {bitWidth : Nat}
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
theorem batchFailure_le_147Over256 {bitWidth : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth) :
    batchFailure bitWidth ≤ ENNReal.ofReal ((147 : Real) / 256) := by
  rw [show (147 : Real) / 256 = 1 - 109 / 256 by norm_num,
    ENNReal.ofReal_sub 1 (by norm_num : (0 : Real) ≤ 109 / 256),
    ENNReal.ofReal_one]
  exact tsub_le_tsub_left
    (oneHundredNineOver256_le_successFloor effective) 1

/-- The canonical conditional-failure calibration lies strictly between zero
and one. -/
theorem conditionalFailureBudget_strictlyWellFormed :
    conditionalFailureBudget.StrictlyWellFormed := by
  refine {
    numerator_pos := ?_
    denominator_pos := ?_
    numerator_le_denominator := ?_
    numerator_lt_denominator := ?_ } <;>
    norm_num [conditionalFailureBudget]

@[simp] theorem conditionalFailureBudget_value :
    conditionalFailureBudget.value = (147 : Real) / 256 := by
  norm_num [conditionalFailureBudget, FailureBudget.value]

/-- Halving a well-formed caller target preserves its well-formedness. -/
theorem retryTargetBudget_wellFormed (budget : FailureBudget)
    (wellFormed : budget.WellFormed) :
    (retryTargetBudget budget).WellFormed := by
  constructor
  · exact wellFormed.numerator_pos
  · exact Nat.mul_pos (by norm_num) wellFormed.denominator_pos
  · change budget.failureNumerator ≤ 2 * budget.failureDenominator
    exact wellFormed.numerator_le_denominator.trans (by omega)

@[simp] theorem retryTargetBudget_value (budget : FailureBudget) :
    (retryTargetBudget budget).value = budget.value / 2 := by
  by_cases denominatorZero : budget.failureDenominator = 0
  · simp [retryTargetBudget, FailureBudget.value, denominatorZero]
  · unfold retryTargetBudget FailureBudget.value
    have denominatorReal : (budget.failureDenominator : Real) ≠ 0 := by
      exact_mod_cast denominatorZero
    field_simp
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    ring

/-- The calibrated independent-retry failure power is at most half of the
caller's declared target. -/
theorem retryBatchFailure_le_halfTarget {bitWidth : Nat}
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    batchFailure bitWidth ^ retryCount budget ≤
      ENNReal.ofReal (budget.value / 2) := by
  calc
    batchFailure bitWidth ^ retryCount budget ≤
        ENNReal.ofReal ((147 : Real) / 256) ^ retryCount budget :=
      pow_le_pow_left' (batchFailure_le_147Over256 effective) _
    _ = ENNReal.ofReal conditionalFailureBudget.value ^ retryCount budget := by
      rw [conditionalFailureBudget_value]
    _ ≤ ENNReal.ofReal (retryTargetBudget budget).value := by
      unfold retryCount
      exact FailureBudget.retryFailurePowerFor_le conditionalFailureBudget
        (retryTargetBudget budget)
        conditionalFailureBudget_strictlyWellFormed
        (retryTargetBudget_wellFormed budget wellFormed)
    _ = ENNReal.ofReal (budget.value / 2) := by
      rw [retryTargetBudget_value]


/-- The original exact calibration supplies positivity without another caller hypothesis. -/
theorem retryCount_pos (budget : FailureBudget) : 0 < retryCount budget :=
  FailureBudget.retryCountFor_pos conditionalFailureBudget (retryTargetBudget budget)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry.Calibration
