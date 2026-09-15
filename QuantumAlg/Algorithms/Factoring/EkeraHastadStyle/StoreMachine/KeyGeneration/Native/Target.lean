/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.KeyGeneration.Native.Probability

/-!
# Original rational targets for actual key-averaged finite retry

The original rational retry calibration reserves half of the target for
conditional retry failure. The key exception is charged once outside the
retry power. When that one-time loss fits the other half, the actual key
average meets the target. The original vanishing key-loss bound supplies
this condition eventually in the prime width, not at every width. The
separate fixed-seven-round calibration is unchanged.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeKeyGeneration

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- The calibrated actual key average meets a rational target when key loss fits its half. -/
theorem success_ge_target_of_keyBound {bitWidth : Nat}
    (nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth))
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth)
    (budget : FailureBudget) (wellFormed : budget.WellFormed)
    {Reference : Register}
    (inputs : RSA.RSAKeyPairBits bitWidth → Execution.Input base Reference)
    (keyBound : ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound bitWidth) ≤
      ENNReal.ofReal (budget.value / 2)) :
    FailureBudget.successThreshold budget ≤
      successMass base noQuantum bitWidth nonempty
        (NativeFiniteRetry.Calibration.retryCount budget) inputs := by
  apply le_trans _ (success_ge_rounds base noQuantum bitWidth nonempty
    (NativeFiniteRetry.Calibration.retryCount budget) inputs effective)
  unfold FailureBudget.successThreshold
  rw [ENNReal.ofReal_sub 1 (FailureBudget.value_nonneg budget wellFormed),
    ENNReal.ofReal_one]
  apply tsub_le_tsub_left
  calc
    keyFailureBound bitWidth + NativeFiniteRetry.Calibration.batchFailure bitWidth ^
        NativeFiniteRetry.Calibration.retryCount budget ≤
      ENNReal.ofReal (budget.value / 2) + ENNReal.ofReal (budget.value / 2) :=
      add_le_add keyBound
        (NativeFiniteRetry.Calibration.retryBatchFailure_le_halfTarget effective budget wellFormed)
    _ = ENNReal.ofReal budget.value := by
      rw [← ENNReal.ofReal_add
        (div_nonneg (FailureBudget.value_nonneg budget wellFormed) (by norm_num))
        (div_nonneg (FailureBudget.value_nonneg budget wellFormed) (by norm_num))]
      congr 1
      ring

/-- Every original well-formed rational target is met at all sufficiently large same-bit widths. -/
theorem eventually_success_ge_target (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    ∀ᶠ bitWidth in Filter.atTop,
      ∀ nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth),
        RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth →
        ∀ (Reference : Register)
          (inputs : RSA.RSAKeyPairBits bitWidth → Execution.Input base Reference),
          FailureBudget.successThreshold budget ≤
            successMass base noQuantum bitWidth nonempty
              (NativeFiniteRetry.Calibration.retryCount budget) inputs := by
  have halfPositive : 0 < budget.value / 2 := by
    have valuePositive := FailureBudget.value_pos budget wellFormed
    positivity
  have eventuallyKey : ∀ᶠ bitWidth in Filter.atTop,
      RSA.GeneratorOrder.keyFailureBound bitWidth < budget.value / 2 :=
    (tendsto_order.1 RSA.GeneratorOrder.keyFailureBound_tendsto_zero).2 _ halfPositive
  filter_upwards [eventuallyKey] with bitWidth keySmall
  intro nonempty effective Reference inputs
  exact success_ge_target_of_keyBound base noQuantum nonempty effective budget wellFormed inputs
    (ENNReal.ofReal_le_ofReal keySmall.le)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeKeyGeneration
