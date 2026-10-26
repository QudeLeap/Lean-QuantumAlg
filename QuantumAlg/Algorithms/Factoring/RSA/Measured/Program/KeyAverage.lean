/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Components.Classical.Model.BitWord

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
public import
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration
public import QuantumAlg.Core.Base.Model
public import QuantumAlg.Core.Execution.Input.Oracle
public import QuantumAlg.Util.PMF

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Success
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Distribution
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Sampled
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Calibration
import
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Probability
import all QuantumAlg.Util.RSA.KeyGeneration
import all QuantumAlg.Util.RSA.GeneratorOrder
import all QuantumAlg.Util.PMF
import QuantumAlg.Core.Base.Classical.Oracle

/-!
# Original ordered-key success of the actual measured constant-workspace RSA parent

The original exact-width ordered key is drawn once. Each generated modulus
then executes the actual measured parent, with arbitrary key-dependent
incoming Store and external reference state. Its own conditional batch failure
is raised to the count before averaging. The exceptional-key loss is charged
once, outside that power.

Only the new parent's actual PMF and soundness theorems certify execution.
The real calibration and the separate fixed-seven RSA-2048 calibration are
pure scalar bounds. Natural counts include zero; no good-key certificate is
required of a runtime input.
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program.KeyAverage

noncomputable section

variable [configuration : Configuration]

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution EkeraHastadStyle.Canonical

local instance {A : Type} : DecidableEq A := Classical.decEq A

/-- The observed factor belongs to the same ordered key branch that generated its modulus. -/
public def successEvent : Set (Nat × Nat × Option Nat) :=
  {triple | ∃ factor, triple.2.2 = some factor ∧
    (factor = triple.1 ∨ factor = triple.2.1)}

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (bitWidth : Nat) (nonempty : Nonempty (QuantumAlg.RSA.RSAKeyPairBits bitWidth))
  (count : Nat) {Reference : Register}
  (inputs : QuantumAlg.RSA.RSAKeyPairBits bitWidth →
    OracleInput ClassicalOracleModel.empty base Reference)

/-- The original uniform ordered keys followed by the actual new run for each public modulus. -/
public def keygenOutputDistribution : PMF (Nat × Nat × Option Nat) :=
  (QuantumAlg.RSA.RSAKeyGenBits bitWidth nonempty).bind fun pair =>
    ((run base noQuantum pair.modulus (inputOfKeyPair pair) count).outputDistribution environment
      (inputs pair)).map fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output)

/-- Declared-prime success in the original key average of the actual parent. -/
public def successMass : ENNReal :=
  (keygenOutputDistribution (environment := environment)
    base noQuantum bitWidth nonempty count inputs).toOuterMeasure
    successEvent

/-- Empty output in that same actual ordered-key average. -/
public def failureMass : ENNReal :=
  (keygenOutputDistribution (environment := environment)
    base noQuantum bitWidth nonempty count inputs).toOuterMeasure
    {triple | triple.2.2 = none}

omit configuration in
private lemma rsaMeasuredKeyAverage_mapped_decode_none_mass (N left right : Nat)
    (distribution : PMF (LatticeBatchRecoveryOutput.OutputShape N).Value) :
    (distribution.map (fun output =>
      (left, right, NativeRetrySelection.decodeFactor output))).toOuterMeasure
        {triple | triple.2.2 = none} = distribution CShape.Value.optionNone := by
  rw [PMF.toOuterMeasure_map_apply]
  change distribution.toOuterMeasure
    {output | NativeRetrySelection.decodeFactor output = none} = _
  have empty : {output : (LatticeBatchRecoveryOutput.OutputShape N).Value |
      NativeRetrySelection.decodeFactor output = none} = {CShape.Value.optionNone} := by
    ext output
    change NativeRetrySelection.decodeFactor output = none ↔ output = CShape.Value.optionNone
    cases output with
    | optionNone => constructor <;> intro _ <;> rfl
    | optionSome word =>
        change some word.toNat = (none : Option Nat) ↔ _
        simp only [reduceCtorEq]
  rw [empty, PMF.toOuterMeasure_apply_singleton]

omit configuration in
private lemma rsaMeasuredKeyAverage_keygen_bind_noneMass_eq
    (distribution : PMF (QuantumAlg.RSA.RSAKeyPairBits bitWidth))
    (kernel : (pair : QuantumAlg.RSA.RSAKeyPairBits bitWidth) →
      PMF (LatticeBatchRecoveryOutput.OutputShape pair.modulus).Value)
    (failure : QuantumAlg.RSA.RSAKeyPairBits bitWidth → ENNReal)
    (noneLaw : ∀ pair, kernel pair CShape.Value.optionNone = failure pair) :
    (distribution.bind fun pair =>
      (kernel pair).map (fun output =>
        (pair.p, pair.q, NativeRetrySelection.decodeFactor output))).toOuterMeasure
          {triple | triple.2.2 = none} =
      ∑' pair, distribution pair * failure pair := by
  rw [PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro pair
  exact congrArg (fun mass : ENNReal =>
    distribution pair * mass)
    ((rsaMeasuredKeyAverage_mapped_decode_none_mass pair.modulus pair.p pair.q (kernel
    pair)).trans (noneLaw pair))

private lemma rsaMeasuredKeyAverage_branch_successMass_eq (pair : QuantumAlg.RSA.RSAKeyPairBits
    bitWidth) :
    (((run base noQuantum pair.modulus (inputOfKeyPair pair) count).outputDistribution environment
      (inputs pair)).map
        (fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output))).toOuterMeasure
          successEvent =
      ((run base noQuantum pair.modulus (inputOfKeyPair pair) count).outputDistribution environment
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
      have sound := rsaMeasuredParent_run_some_sound base noQuantum
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

/-- Each original key keeps its own conditional retry power, also at count zero. -/
lemma rsaMeasuredKeyAverage_branch_successProbability (pair : QuantumAlg.RSA.RSAKeyPairBits
    bitWidth) :
    (((run base noQuantum pair.modulus (inputOfKeyPair pair) count).outputDistribution environment
      (inputs pair)).map
        (fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output))).toOuterMeasure
          successEvent =
      1 - sampledBatchOutputPMFAtCount (inputOfKeyPair pair) membersPerBatch none ^ count := by
  rw [rsaMeasuredKeyAverage_branch_successMass_eq, rsaMeasuredParent_run_successProbability]

/-- Exact success averages the original key's retry power after fixing that key. -/
lemma rsaMeasuredKeyAverage_successMass_eq :
    successMass (environment := environment) base noQuantum bitWidth nonempty count inputs =
      ∑' pair, QuantumAlg.RSA.RSAKeyGenBits bitWidth nonempty pair *
        (1 - sampledBatchOutputPMFAtCount (inputOfKeyPair pair) membersPerBatch none ^ count) := by
  rw [successMass, keygenOutputDistribution, PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro pair
  rw [rsaMeasuredKeyAverage_branch_successProbability]

/-- Exact failure averages per-key powers, rather than taking a power of the averaged failure. -/
lemma rsaMeasuredKeyAverage_failureMass_eq :
    failureMass (environment := environment) base noQuantum bitWidth nonempty count inputs =
      ∑' pair, QuantumAlg.RSA.RSAKeyGenBits bitWidth nonempty pair *
        sampledBatchOutputPMFAtCount (inputOfKeyPair pair) membersPerBatch none ^ count := by
  exact rsaMeasuredKeyAverage_keygen_bind_noneMass_eq bitWidth
    (QuantumAlg.RSA.RSAKeyGenBits bitWidth nonempty)
    (fun pair => (run base noQuantum pair.modulus (inputOfKeyPair pair) count).outputDistribution
      environment
      (inputs pair))
    (fun pair => sampledBatchOutputPMFAtCount (inputOfKeyPair pair) membersPerBatch none ^ count)
    (fun pair =>
      rsaMeasuredParent_run_none base noQuantum (inputOfKeyPair pair) count (inputs pair))

/-- The one-time key exception is the original exact-width common-divisor tail. -/
private def keyFailureBound (width : Nat) : ENNReal :=
  ENNReal.ofReal (QuantumAlg.RSA.GeneratorOrder.keyFailureBound width)

omit configuration in
private lemma rsaMeasuredKeyAverage_goodKeyMass_ge
    (effective : QuantumAlg.RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth) :
    1 - keyFailureBound bitWidth ≤
      (QuantumAlg.RSA.RSAKeyGenBits bitWidth nonempty).toOuterMeasure
        {pair | ¬ 2 ^ QuantumAlg.RSA.GeneratorOrder.gcdLossBits bitWidth ≤
          Nat.gcd (pair.p - 1) (pair.q - 1)} := by
  rw [PMF.eventProbability_eq_one_sub_complement]
  simp only [not_not]
  rw [QuantumAlg.RSA.GeneratorOrder.RSAKeyGenBits_commonDivisorBadMass_eq]
  exact tsub_le_tsub_left (ENNReal.ofReal_le_ofReal
    (QuantumAlg.RSA.GeneratorOrder.keyGenerationBadFraction_le_keyFailureBound effective)) 1

private lemma rsaMeasuredKeyAverage_successMass_ge_goodKeyMass
    (effective : QuantumAlg.RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth) :
    (QuantumAlg.RSA.RSAKeyGenBits bitWidth nonempty).toOuterMeasure
        {pair | ¬ 2 ^ QuantumAlg.RSA.GeneratorOrder.gcdLossBits bitWidth ≤
          Nat.gcd (pair.p - 1) (pair.q - 1)} *
      ((1 : ENNReal) - NativeFiniteRetry.Calibration.batchFailure bitWidth ^ count) ≤
    successMass (environment := environment) base noQuantum bitWidth nonempty count inputs := by
  let exceptional : QuantumAlg.RSA.RSAKeyPairBits bitWidth → Prop := fun pair =>
    2 ^ QuantumAlg.RSA.GeneratorOrder.gcdLossBits bitWidth ≤ Nat.gcd (pair.p - 1) (pair.q - 1)
  unfold successMass keygenOutputDistribution
  apply PMF.bind_eventProbability_ge_goodMass_mul
    (exceptional := exceptional) (event := fun triple => triple ∈ successEvent)
  intro pair pairGood
  change (1 : ENNReal) - NativeFiniteRetry.Calibration.batchFailure bitWidth ^ count ≤
    (((run base noQuantum pair.modulus (inputOfKeyPair pair) count).outputDistribution environment
      (inputs pair)).map
        (fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output))).toOuterMeasure
          successEvent
  rw [rsaMeasuredKeyAverage_branch_successProbability]
  let key : GoodKeyModel pair.modulus :=
    ⟨bitWidth, pair, rfl, effective, Nat.lt_of_not_ge pairGood⟩
  exact tsub_le_tsub_left
    (pow_le_pow_left' (NativeBatchSuccess.sampled_none_le_of_count_ge key
      (by have original := configuration.originalMembers;
          unfold membersPerBatch; omega)) count) (1 : ENNReal)

omit configuration in
private lemma rsaMeasuredKeyAverage_successFloor_of_goodMass_lower (keyLoss retryLoss goodMass
    totalMass : ENNReal)
    (goodLower : (1 : ENNReal) - keyLoss ≤ goodMass)
    (conditionalLower : goodMass * ((1 : ENNReal) - retryLoss) ≤ totalMass) :
    (1 : ENNReal) - (keyLoss + retryLoss) ≤ totalMass := by
  have weighted :
      ((1 : ENNReal) - keyLoss) * ((1 : ENNReal) - retryLoss) ≤
        goodMass * ((1 : ENNReal) - retryLoss) :=
    mul_le_mul_left (α := ENNReal) goodLower ((1 : ENNReal) - retryLoss)
  exact le_trans
    (a := (1 : ENNReal) - (keyLoss + retryLoss))
    (b := ((1 : ENNReal) - keyLoss) * ((1 : ENNReal) - retryLoss))
    (c := totalMass)
    (PMF.one_sub_add_le_mul_one_sub keyLoss retryLoss)
    (le_trans
      (a := ((1 : ENNReal) - keyLoss) * ((1 : ENNReal) - retryLoss))
      (b := goodMass * ((1 : ENNReal) - retryLoss))
      (c := totalMass) weighted conditionalLower)

/-- A bound on each original good key's actual configured batch failure
is lifted through the original ordered-key law without resampling the key. -/
lemma rsaMeasuredKeyAverage_success_ge_rounds_of_batchBound
    (effective : QuantumAlg.RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth)
    (failure : ENNReal)
    (bounded : ∀ pair : QuantumAlg.RSA.RSAKeyPairBits bitWidth,
      Nat.gcd (pair.p - 1) (pair.q - 1) <
          2 ^ QuantumAlg.RSA.GeneratorOrder.gcdLossBits bitWidth →
        sampledBatchOutputPMFAtCount (inputOfKeyPair pair) membersPerBatch none ≤ failure) :
    1 - (ENNReal.ofReal (QuantumAlg.RSA.GeneratorOrder.keyFailureBound bitWidth) +
      failure ^ count) ≤
      successMass (environment := environment) base noQuantum bitWidth nonempty count inputs := by
  apply rsaMeasuredKeyAverage_successFloor_of_goodMass_lower
    (keyFailureBound bitWidth) (failure ^ count)
    ((QuantumAlg.RSA.RSAKeyGenBits bitWidth nonempty).toOuterMeasure
      {pair | ¬ 2 ^ QuantumAlg.RSA.GeneratorOrder.gcdLossBits bitWidth ≤
        Nat.gcd (pair.p - 1) (pair.q - 1)})
    (successMass (environment := environment) base noQuantum bitWidth nonempty count inputs)
    (rsaMeasuredKeyAverage_goodKeyMass_ge bitWidth nonempty effective)
  let exceptional : QuantumAlg.RSA.RSAKeyPairBits bitWidth → Prop := fun pair =>
    2 ^ QuantumAlg.RSA.GeneratorOrder.gcdLossBits bitWidth ≤ Nat.gcd (pair.p - 1) (pair.q - 1)
  unfold successMass keygenOutputDistribution
  apply PMF.bind_eventProbability_ge_goodMass_mul
    (exceptional := exceptional) (event := fun triple => triple ∈ successEvent)
  intro pair pairGood
  change (1 : ENNReal) - failure ^ count ≤
    (((run base noQuantum pair.modulus (inputOfKeyPair pair) count).outputDistribution environment
      (inputs pair)).map
        (fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output))).toOuterMeasure
          successEvent
  rw [rsaMeasuredKeyAverage_branch_successProbability]
  exact tsub_le_tsub_left
    (pow_le_pow_left' (bounded pair (Nat.lt_of_not_ge pairGood)) count) (1 : ENNReal)

/-- All original keys are admitted; their exception is charged once outside finite retry. -/
lemma rsaMeasuredKeyAverage_success_ge_rounds
    (effective : QuantumAlg.RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth) :
    1 - (ENNReal.ofReal (QuantumAlg.RSA.GeneratorOrder.keyFailureBound bitWidth) +
      NativeFiniteRetry.Calibration.batchFailure bitWidth ^ count) ≤
      successMass (environment := environment) base noQuantum bitWidth nonempty count inputs := by
  exact rsaMeasuredKeyAverage_successFloor_of_goodMass_lower
    (keyFailureBound bitWidth)
    (NativeFiniteRetry.Calibration.batchFailure bitWidth ^ count)
    ((QuantumAlg.RSA.RSAKeyGenBits bitWidth nonempty).toOuterMeasure
      {pair | ¬ 2 ^ QuantumAlg.RSA.GeneratorOrder.gcdLossBits bitWidth ≤
        Nat.gcd (pair.p - 1) (pair.q - 1)})
    (successMass (environment := environment) base noQuantum bitWidth nonempty count inputs)
    (rsaMeasuredKeyAverage_goodKeyMass_ge bitWidth nonempty effective)
    (rsaMeasuredKeyAverage_successMass_ge_goodKeyMass base noQuantum bitWidth nonempty count
    inputs effective)

/-- The calibrated actual key average meets a real target when key loss fits its half. -/
lemma rsaMeasuredKeyAverage_success_ge_target_of_keyBound
    (effective : QuantumAlg.RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth)
    (η : Real) (positive : 0 < η)
    (keyBound : ENNReal.ofReal (QuantumAlg.RSA.GeneratorOrder.keyFailureBound bitWidth) ≤
      ENNReal.ofReal (η / 2)) :
    ENNReal.ofReal (1 - η) ≤
      successMass (environment := environment) base noQuantum bitWidth nonempty
        (NativeFiniteRetry.Calibration.retryCount η) inputs := by
  exact NativeFiniteRetry.Calibration.realFailureCalibration_twoHalvesSuccess
    η positive _ _ _ keyBound
    (NativeFiniteRetry.Calibration.retryBatchFailure_le_halfTarget effective η positive)
    (rsaMeasuredKeyAverage_success_ge_rounds base noQuantum bitWidth nonempty
      (NativeFiniteRetry.Calibration.retryCount η) inputs effective)

/-- Every positive real target is met eventually on the original ordered exact-width keys. -/
public lemma rsaMeasuredKeyAverage_eventually_success_ge_target (η : Real) (positive : 0 < η) :
    ∀ᶠ width in Filter.atTop,
      ∀ populated : Nonempty (QuantumAlg.RSA.RSAKeyPairBits width),
        QuantumAlg.RSA.GeneratorOrder.effectiveCutoffBits ≤ width →
        ∀ (External : Register)
          (initials : QuantumAlg.RSA.RSAKeyPairBits width →
            OracleInput ClassicalOracleModel.empty base External),
          ENNReal.ofReal (1 - η) ≤
            successMass (environment := environment) base noQuantum width populated
              (NativeFiniteRetry.Calibration.retryCount η) initials := by
  have halfPositive : 0 < η / 2 := div_pos positive (by norm_num)
  have eventuallyKey : ∀ᶠ width in Filter.atTop,
      QuantumAlg.RSA.GeneratorOrder.keyFailureBound width < η / 2 :=
    (tendsto_order.1 QuantumAlg.RSA.GeneratorOrder.keyFailureBound_tendsto_zero).2 _ halfPositive
  filter_upwards [eventuallyKey] with width keySmall
  intro populated effective external initials
  exact rsaMeasuredKeyAverage_success_ge_target_of_keyBound base noQuantum width populated
    initials effective
    η positive (ENNReal.ofReal_le_ofReal keySmall.le)

/-- RSA-2048 retains its independent seven-batch calculation, not the generic one-percent count. -/
public lemma rsaMeasuredKeyAverage_fixedSeven_success_ge_99
    (populated : Nonempty (QuantumAlg.RSA.RSAKeyPairBits 1024))
    {External : Register}
    (initials : QuantumAlg.RSA.RSAKeyPairBits 1024 →
      OracleInput ClassicalOracleModel.empty base External) :
    ENNReal.ofReal ((99 : Real) / 100) ≤
      successMass (environment := environment) base noQuantum 1024 populated 7 initials := by
  exact NativeRSA2048.Calibration.combinedSuccess_seven_ge_99.trans
    (rsaMeasuredKeyAverage_success_ge_rounds base noQuantum 1024 populated 7 initials (by
      norm_num [QuantumAlg.RSA.GeneratorOrder.effectiveCutoffBits]))

end

end QuantumAlg.Factoring.RSA.Measured.Program.KeyAverage
