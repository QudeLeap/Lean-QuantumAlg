/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Endpoint
import all QuantumAlg.Util.RSA.KeyGeneration

/-!
# Original key averaging of the actual original-width oracle run

Each original ordered same-bit key is chosen once, then its public modulus
is passed to the actual finite original-bank execution. The initial input
may depend on that key and carry any external reference. Key generation is
a theorem-side average, not an additional circuit instruction. The key
exception is charged once outside the retry power and shares the original
failure target with the conditional execution's half-budget.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def keySuccessEvent : Set (Nat × Nat × Option Nat) :=
  {triple | ∃ factor, triple.2.2 = some factor ∧
    (factor = triple.1 ∨ factor = triple.2.1)}

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (bitWidth : Nat) (nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth))
    (count : Nat) {Reference : Register}
    (inputs : RSA.RSAKeyPairBits bitWidth → Execution.Input base Reference)

/-- The original ordered key law followed by this actual original-bank finite run in each branch. -/
public def keygenOutputDistribution : PMF (Nat × Nat × Option Nat) :=
  (RSA.RSAKeyGenBits bitWidth nonempty).bind fun pair =>
    ((Retry.Finite.run base noQuantum pair.modulus (inputOfKeyPair pair) count).outputDistribution
      (inputs pair)).map fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output)

/-- The same actual output observation succeeds only on a prime generated in its own key branch. -/
public def keygenSuccessMass : ENNReal :=
  (keygenOutputDistribution base noQuantum bitWidth nonempty count inputs).toOuterMeasure
    keySuccessEvent

private theorem branch_success (pair : RSA.RSAKeyPairBits bitWidth) :
    (((Retry.Finite.run base noQuantum pair.modulus (inputOfKeyPair pair) count).outputDistribution
      (inputs pair)).map
        (fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output))).toOuterMeasure
          keySuccessEvent =
      ((Retry.Finite.run base noQuantum pair.modulus (inputOfKeyPair pair) count).outputDistribution
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
      have sound := Retry.Finite.nativeOracle_finiteRetry_some_sound base noQuantum pair.modulus
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

/-- Actual key-averaged success applies the retry power within each original key branch. -/
theorem nativeOracle_keygenSuccessMass_eq :
    keygenSuccessMass base noQuantum bitWidth nonempty count inputs =
      ∑' pair, RSA.RSAKeyGenBits bitWidth nonempty pair *
        (1 - sampledBatchOutputPMF (inputOfKeyPair pair) none ^ count) := by
  rw [keygenSuccessMass, keygenOutputDistribution, PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro pair
  rw [branch_success, Retry.Finite.nativeOracle_finiteRetry_successProbability]

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

/-- The original key exception is charged once, alongside the actual conditional half-target. -/
theorem nativeOracle_keygen_success_ge
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    1 - (ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound bitWidth) +
      ENNReal.ofReal (budget.value / 2)) ≤
      keygenSuccessMass base noQuantum bitWidth nonempty (calibratedCount budget) inputs := by
  let exceptional : RSA.RSAKeyPairBits bitWidth → Prop := fun pair =>
    2 ^ RSA.GeneratorOrder.gcdLossBits bitWidth ≤ Nat.gcd (pair.p - 1) (pair.q - 1)
  have bindLower :
      (RSA.RSAKeyGenBits bitWidth nonempty).toOuterMeasure {pair | ¬ exceptional pair} *
        (1 - ENNReal.ofReal (budget.value / 2)) ≤
      keygenSuccessMass base noQuantum bitWidth nonempty (calibratedCount budget) inputs := by
    unfold keygenSuccessMass keygenOutputDistribution
    apply PMF.bind_eventProbability_ge_goodMass_mul
      (exceptional := exceptional) (event := fun triple => triple ∈ keySuccessEvent)
    intro pair pairGood
    change 1 - ENNReal.ofReal (budget.value / 2) ≤
      (((Retry.Finite.run base noQuantum pair.modulus (inputOfKeyPair pair)
        (calibratedCount budget)).outputDistribution (inputs pair)).map
          (fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output))).toOuterMeasure
            keySuccessEvent
    rw [branch_success]
    let model : GoodKeyModel pair.modulus :=
      ⟨bitWidth, pair, rfl, effective, Nat.lt_of_not_ge pairGood⟩
    have conditional := (tsub_le_tsub_left
      (NativeFiniteRetry.Calibration.retryBatchFailure_le_halfTarget
        model.effective budget wellFormed) 1).trans
      (Retry.Finite.nativeOracle_finiteRetry_successProbability_ge base noQuantum pair.modulus
        model (calibratedCount budget) (inputs pair))
    simpa only [model, GoodKeyModel.input, inputOfKeyPair] using conditional
  calc
    1 - (ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound bitWidth) +
        ENNReal.ofReal (budget.value / 2)) ≤
      (1 - ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound bitWidth)) *
        (1 - ENNReal.ofReal (budget.value / 2)) := PMF.one_sub_add_le_mul_one_sub _ _
    _ ≤ (RSA.RSAKeyGenBits bitWidth nonempty).toOuterMeasure {pair | ¬ exceptional pair} *
        (1 - ENNReal.ofReal (budget.value / 2)) := by
      simpa only [mul_comm] using
        mul_le_mul_right (good_key_mass bitWidth nonempty effective)
          (1 - ENNReal.ofReal (budget.value / 2))
    _ ≤ _ := bindLower

/-- Fitting the one-time key exception in its original half-budget gives the full target. -/
theorem nativeOracle_keygen_success_ge_target
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth)
    (budget : FailureBudget) (wellFormed : budget.WellFormed)
    (keyBound : ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound bitWidth) ≤
      ENNReal.ofReal (budget.value / 2)) :
    FailureBudget.successThreshold budget ≤
      keygenSuccessMass base noQuantum bitWidth nonempty (calibratedCount budget) inputs := by
  apply le_trans _
    (nativeOracle_keygen_success_ge base noQuantum bitWidth nonempty inputs effective
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

/-- The same actual original-width run reaches every original target on eventual same-bit keys. -/
theorem eventually_nativeOracle_keygen_success_ge_target
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    ∀ᶠ bitWidth in Filter.atTop,
      ∀ nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth),
        RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth →
        ∀ {Reference : Register}
          (inputs : RSA.RSAKeyPairBits bitWidth → Execution.Input base Reference),
          FailureBudget.successThreshold budget ≤
            keygenSuccessMass base noQuantum bitWidth nonempty (calibratedCount budget) inputs := by
  have halfPositive : 0 < budget.value / 2 := by
    have valuePositive := FailureBudget.value_pos budget wellFormed
    positivity
  have eventuallyKey : ∀ᶠ bitWidth in Filter.atTop,
      RSA.GeneratorOrder.keyFailureBound bitWidth < budget.value / 2 :=
    (tendsto_order.1 RSA.GeneratorOrder.keyFailureBound_tendsto_zero).2 _ halfPositive
  filter_upwards [eventuallyKey] with width keySmall
  intro populated effective reference inputs
  exact nativeOracle_keygen_success_ge_target base noQuantum width populated inputs effective
    budget wellFormed (ENNReal.ofReal_le_ofReal keySmall.le)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native
