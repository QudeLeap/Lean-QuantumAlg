/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration
import all QuantumAlg.Util.RSA.KeyGeneration

/-!
# Original ordered-key success for the completed EH execution

Every key is sampled once. The direct completed source law supplies the
conditional retry bound; the independent common-divisor tail pays the key
exception once outside that power. Initial caller, service and reference
states may depend on the sampled key.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

private def keySuccessEvent : Set (Nat × Nat × Option Nat) :=
  {triple | ∃ factor, triple.2.2 = some factor ∧
    (factor = triple.1 ∨ factor = triple.2.1)}

section KeyAverage

variable (bitWidth : Nat) (nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth))
  (count : Nat) {Reference : Register}
  (inputs : (pair : RSA.RSAKeyPairBits bitWidth) →
    Execution.OracleInput (model (inputOfKeyPair pair)).classicalOracles base Reference)

/-- The original ordered key law followed by the actual completed run with each fixed model. -/
public def completedKeygenOutputDistribution : PMF (Nat × Nat × Option Nat) :=
  (RSA.RSAKeyGenBits bitWidth nonempty).bind fun pair =>
    ((completedAlgorithm base noQuantum (inputOfKeyPair pair) count).run.outputDistribution
      (inputs pair)).map fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output)

/-- Success observes the actual factor from the same generated key branch. -/
public def completedKeygenSuccessMass : ENNReal :=
  (completedKeygenOutputDistribution base noQuantum bitWidth nonempty count inputs).toOuterMeasure
    keySuccessEvent

private theorem branch_success (pair : RSA.RSAKeyPairBits bitWidth) :
    (((completedAlgorithm base noQuantum (inputOfKeyPair pair) count).run.outputDistribution
      (inputs pair)).map
        (fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output))).toOuterMeasure
          keySuccessEvent =
      ((completedAlgorithm base noQuantum (inputOfKeyPair pair) count).run.outputDistribution
        (inputs pair)).toOuterMeasure {output | output ≠ CShape.Value.optionNone} := by
  rw [PMF.toOuterMeasure_map_apply]
  apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
  ext output
  simp only [Set.mem_inter_iff]
  apply and_congr_left
  intro supported
  cases output with
  | optionNone =>
      change (∃ factor, (none : Option Nat) = some factor ∧
        (factor = pair.p ∨ factor = pair.q)) ↔
        (CShape.Value.optionNone :
          (LatticeBatchRecoveryOutput.OutputShape pair.modulus).Value) ≠ .optionNone
      simp only [reduceCtorEq, false_and, exists_false, ne_eq, not_true_eq_false]
  | optionSome word =>
      have sound := completedAlgorithm_some_sound base noQuantum
        (inputOfKeyPair pair) count (inputs pair) word supported
      have declared := (semiprimeOfKeyPair pair).nontrivial_factor_eq_declared
        sound.1 sound.2.1 sound.2.2
      change (∃ factor, some word.toNat = some factor ∧
        (factor = pair.p ∨ factor = pair.q)) ↔ _
      constructor
      · intro _ impossible
        cases impossible
      · intro _
        exact ⟨word.toNat, rfl, declared⟩

/-- The actual key average retains the conditional failure power inside each original key. -/
theorem completedFinite_completedKeygenSuccessMass_eq :
    completedKeygenSuccessMass base noQuantum bitWidth nonempty count inputs =
      ∑' pair, RSA.RSAKeyGenBits bitWidth nonempty pair *
        (1 - sampledBatchOutputPMF (inputOfKeyPair pair) none ^ count) := by
  change ((RSA.RSAKeyGenBits bitWidth nonempty).bind fun pair =>
    ((completedAlgorithm base noQuantum (inputOfKeyPair pair) count).run.outputDistribution
      (inputs pair)).map fun output =>
        (pair.p, pair.q, NativeRetrySelection.decodeFactor output)).toOuterMeasure
          keySuccessEvent = _
  rw [PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro pair
  rw [branch_success, completedAlgorithm_populatedProbability]
  rfl

private theorem good_key_mass (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth) :
    1 - ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound bitWidth) ≤
      (RSA.RSAKeyGenBits bitWidth nonempty).toOuterMeasure
        {pair | ¬ 2 ^ RSA.GeneratorOrder.gcdLossBits bitWidth ≤
          Nat.gcd (pair.p - 1) (pair.q - 1)} := by
  rw [PMF.eventProbability_eq_one_sub_complement]
  simp only [not_not]
  rw [RSA.GeneratorOrder.RSAKeyGenBits_commonDivisorBadMass_eq]
  exact tsub_le_tsub_left (ENNReal.ofReal_le_ofReal
    (RSA.GeneratorOrder.keyGenerationBadFraction_le_keyFailureBound effective)) 1

private theorem good_branch_floor (pair : RSA.RSAKeyPairBits bitWidth)
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth)
    (pairGood : ¬ 2 ^ RSA.GeneratorOrder.gcdLossBits bitWidth ≤
      Nat.gcd (pair.p - 1) (pair.q - 1))
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    1 - ENNReal.ofReal (budget.value / 2) ≤
      (((completedAlgorithm base noQuantum (inputOfKeyPair pair)
        (calibratedCount budget)).run.outputDistribution (inputs pair)).map
          (fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output))).toOuterMeasure
            keySuccessEvent := by
  rw [branch_success]
  let good : GoodKeyModel pair.modulus :=
    ⟨bitWidth, pair, rfl, effective, Nat.lt_of_not_ge pairGood⟩
  have conditional := (tsub_le_tsub_left
    (NativeFiniteRetry.Calibration.retryBatchFailure_le_halfTarget
      good.effective budget wellFormed) 1).trans
    (completedAlgorithm_successProbability_ge base noQuantum
      good (calibratedCount budget) (inputs pair))
  simpa only [good, GoodKeyModel.input, inputOfKeyPair] using conditional

private theorem good_mass_times_floor_le
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    (RSA.RSAKeyGenBits bitWidth nonempty).toOuterMeasure
        {pair | ¬ 2 ^ RSA.GeneratorOrder.gcdLossBits bitWidth ≤
          Nat.gcd (pair.p - 1) (pair.q - 1)} *
      (1 - ENNReal.ofReal (budget.value / 2)) ≤
        completedKeygenSuccessMass base noQuantum bitWidth nonempty
          (calibratedCount budget) inputs := by
  change _ ≤ ((RSA.RSAKeyGenBits bitWidth nonempty).bind fun pair =>
    ((completedAlgorithm base noQuantum (inputOfKeyPair pair)
      (calibratedCount budget)).run.outputDistribution (inputs pair)).map fun output =>
        (pair.p, pair.q, NativeRetrySelection.decodeFactor output)).toOuterMeasure
          keySuccessEvent
  exact PMF.bind_eventProbability_ge_goodMass_mul
    (RSA.RSAKeyGenBits bitWidth nonempty)
    (fun pair => ((completedAlgorithm base noQuantum (inputOfKeyPair pair)
      (calibratedCount budget)).run.outputDistribution (inputs pair)).map fun output =>
        (pair.p, pair.q, NativeRetrySelection.decodeFactor output))
    (fun pair => 2 ^ RSA.GeneratorOrder.gcdLossBits bitWidth ≤
      Nat.gcd (pair.p - 1) (pair.q - 1))
    (fun triple => triple ∈ keySuccessEvent)
    (1 - ENNReal.ofReal (budget.value / 2))
    (fun pair pairGood => good_branch_floor base noQuantum bitWidth inputs pair
      effective pairGood budget wellFormed)

/-- The one-time key exception and conditional half-target bound the actual completed average. -/
theorem completedFinite_keygen_success_ge
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    1 - (ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound bitWidth) +
      ENNReal.ofReal (budget.value / 2)) ≤
      completedKeygenSuccessMass base noQuantum bitWidth nonempty
          (calibratedCount budget) inputs := by
  calc
    1 - (ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound bitWidth) +
        ENNReal.ofReal (budget.value / 2)) ≤
      (1 - ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound bitWidth)) *
        (1 - ENNReal.ofReal (budget.value / 2)) := PMF.one_sub_add_le_mul_one_sub _ _
    _ ≤ (RSA.RSAKeyGenBits bitWidth nonempty).toOuterMeasure
        {pair | ¬ 2 ^ RSA.GeneratorOrder.gcdLossBits bitWidth ≤
          Nat.gcd (pair.p - 1) (pair.q - 1)} *
        (1 - ENNReal.ofReal (budget.value / 2)) := by
      simpa only [mul_comm] using
        mul_le_mul_right (good_key_mass bitWidth nonempty effective)
          (1 - ENNReal.ofReal (budget.value / 2))
    _ ≤ _ := good_mass_times_floor_le base noQuantum bitWidth nonempty inputs
      effective budget wellFormed

/-- When the original one-time key exception fits its half-budget, the full target follows. -/
theorem completedFinite_keygen_success_ge_target
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth)
    (budget : FailureBudget) (wellFormed : budget.WellFormed)
    (keyBound : ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound bitWidth) ≤
      ENNReal.ofReal (budget.value / 2)) :
    FailureBudget.successThreshold budget ≤
      completedKeygenSuccessMass base noQuantum bitWidth nonempty
          (calibratedCount budget) inputs := by
  apply le_trans _
    (completedFinite_keygen_success_ge base noQuantum bitWidth nonempty inputs effective
      budget wellFormed)
  unfold FailureBudget.successThreshold
  rw [ENNReal.ofReal_sub 1 (FailureBudget.value_nonneg budget wellFormed), ENNReal.ofReal_one]
  apply tsub_le_tsub_left
  calc
    ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound bitWidth) +
        ENNReal.ofReal (budget.value / 2) ≤
      ENNReal.ofReal (budget.value / 2) + ENNReal.ofReal (budget.value / 2) :=
        add_le_add keyBound le_rfl
    _ = ENNReal.ofReal budget.value := by
      rw [← ENNReal.ofReal_add
        (div_nonneg (FailureBudget.value_nonneg budget wellFormed) (by norm_num))
        (div_nonneg (FailureBudget.value_nonneg budget wellFormed) (by norm_num))]
      congr 1
      ring

/-- The same completed run reaches every original target on eventual original same-bit keys. -/
theorem eventually_completedFinite_keygen_success_ge_target
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    ∀ᶠ bitWidth in Filter.atTop,
      ∀ nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth),
        RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth →
        ∀ {Reference : Register}
          (inputs : (pair : RSA.RSAKeyPairBits bitWidth) →
            Execution.OracleInput (model (inputOfKeyPair pair)).classicalOracles base Reference),
          FailureBudget.successThreshold budget ≤
            completedKeygenSuccessMass base noQuantum bitWidth nonempty
          (calibratedCount budget) inputs := by
  have halfPositive : 0 < budget.value / 2 := by
    have valuePositive := FailureBudget.value_pos budget wellFormed
    positivity
  have eventuallyKey : ∀ᶠ bitWidth in Filter.atTop,
      RSA.GeneratorOrder.keyFailureBound bitWidth < budget.value / 2 :=
    (tendsto_order.1 RSA.GeneratorOrder.keyFailureBound_tendsto_zero).2 _ halfPositive
  filter_upwards [eventuallyKey] with width keySmall
  intro populated effective reference inputs
  exact completedFinite_keygen_success_ge_target base noQuantum width populated inputs effective
    budget wellFormed (ENNReal.ofReal_le_ofReal keySmall.le)

end KeyAverage

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
