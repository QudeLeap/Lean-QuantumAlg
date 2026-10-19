/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.KeyGeneration.Native.Probability

/-!
# Real targets for actual key-averaged finite retry

The shared real retry calibration reserves half of the target for
conditional retry failure. The key exception is charged once outside the
retry power. When that one-time loss fits the other half, the actual key
average meets the target. The original vanishing key-loss bound supplies
this condition eventually in the prime width, not at every width. The
separate fixed-seven-round calibration is unchanged.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeKeyGeneration

noncomputable section

open ShortDLP.CompiledMAU

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (environment : RuntimeRound.model.Environment)

/-- The calibrated actual key average meets a real target when key loss fits its half. -/
lemma success_ge_target_of_keyBound {bitWidth : Nat}
    (nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth))
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth)
    (η : Real) (etaPositive : 0 < η)
    {Reference : Register}
    (inputs : RSA.RSAKeyPairBits bitWidth →
      Execution.OracleInput RuntimeRound.model.classicalOracles base Reference)
    (keyBound : ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound bitWidth) ≤
      ENNReal.ofReal (η / 2)) :
    ENNReal.ofReal (1 - η) ≤
      successMass base noQuantum bitWidth nonempty
        (NativeFiniteRetry.Calibration.retryCount η) environment inputs := by
  exact NativeFiniteRetry.Calibration.realFailureCalibration_twoHalvesSuccess
    η etaPositive _ _ _ keyBound
    (NativeFiniteRetry.Calibration.retryBatchFailure_le_halfTarget effective η etaPositive)
    (success_ge_rounds base noQuantum bitWidth nonempty
      (NativeFiniteRetry.Calibration.retryCount η) environment inputs effective)

/-- Every positive real target is met at all sufficiently large same-bit widths. -/
lemma eventually_success_ge_target (η : Real) (etaPositive : 0 < η) :
    ∀ᶠ bitWidth in Filter.atTop,
      ∀ nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth),
        RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth →
        ∀ (Reference : Register)
          (inputs : RSA.RSAKeyPairBits bitWidth →
            Execution.OracleInput RuntimeRound.model.classicalOracles base Reference),
          ENNReal.ofReal (1 - η) ≤
            successMass base noQuantum bitWidth nonempty
              (NativeFiniteRetry.Calibration.retryCount η) environment inputs := by
  have halfPositive : 0 < η / 2 := div_pos etaPositive (by norm_num)
  have eventuallyKey : ∀ᶠ bitWidth in Filter.atTop,
      RSA.GeneratorOrder.keyFailureBound bitWidth < η / 2 :=
    (tendsto_order.1 RSA.GeneratorOrder.keyFailureBound_tendsto_zero).2 _ halfPositive
  filter_upwards [eventuallyKey] with bitWidth keySmall
  intro nonempty effective Reference inputs
  exact success_ge_target_of_keyBound base noQuantum environment
    nonempty effective η etaPositive inputs
    (ENNReal.ofReal_le_ofReal keySmall.le)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeKeyGeneration
