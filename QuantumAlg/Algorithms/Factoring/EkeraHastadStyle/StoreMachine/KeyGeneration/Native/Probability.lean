/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Mathlib.Data.Set.Defs

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.KeyGeneration.Native.Distribution
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Success

/-!
# Key-averaged success of actual finite retry

The original uniform key is selected once. Its conditional empty-output
probability is raised to the requested total count, including zero, before
averaging. The exceptional key mass is charged once outside this retry power.
Prime factors and good-key certificates occur only in the mathematical proof;
the actual finite run and its complete typed output are unchanged.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeKeyGeneration

noncomputable section

open Execution ShortDLP.CompiledMAU

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Success observes one of the primes attached by the theorem-side key average. -/
public def successEvent : Set (Nat × Nat × Option Nat) :=
  {triple | ∃ factor, triple.2.2 = some factor ∧
    (factor = triple.1 ∨ factor = triple.2.1)}

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (bitWidth : Nat) (nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth))
    (totalRounds : Nat) {Reference : Register}
    (inputs : RSA.RSAKeyPairBits bitWidth →
      Execution.OracleInput RuntimeRound.model.classicalOracles base Reference)

/-- Actual success mass in the original ordered uniform key average. -/
def successMass : ENNReal :=
  (outputDistribution base noQuantum bitWidth nonempty totalRounds inputs).toOuterMeasure
    successEvent

/-- Actual empty mass in the same original key average. -/
def failureMass : ENNReal :=
  (outputDistribution base noQuantum bitWidth nonempty totalRounds inputs).toOuterMeasure
    {triple | triple.2.2 = none}

/-- In each key branch, declared-prime success is exactly the populated actual output event. -/
theorem branch_successMass_eq (pair : RSA.RSAKeyPairBits bitWidth) :
    (((NativeFiniteRetry.run base noQuantum (inputOfKeyPair pair) totalRounds).outputDistribution
      (inputs pair)).map
        (fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output))).toOuterMeasure
          successEvent =
      ((NativeFiniteRetry.run base noQuantum (inputOfKeyPair pair) totalRounds).outputDistribution
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
      have sound := NativeFiniteRetry.run_some_sound base noQuantum (inputOfKeyPair pair)
        totalRounds (inputs pair) word supported
      have declared := (semiprimeOfKeyPair pair).nontrivial_factor_eq_declared
        sound.1 sound.2.1 sound.2.2
      change (∃ factor, some word.toNat = some factor ∧
        (factor = pair.p ∨ factor = pair.q)) ↔ _
      constructor
      · intro _ impossible
        cases impossible
      · intro _
        exact ⟨word.toNat, rfl, declared⟩

/-- The exact conditional branch success uses the original batch empty probability's power. -/
theorem branch_successProbability (pair : RSA.RSAKeyPairBits bitWidth) :
    (((NativeFiniteRetry.run base noQuantum (inputOfKeyPair pair) totalRounds).outputDistribution
      (inputs pair)).map
        (fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output))).toOuterMeasure
          successEvent =
      1 - sampledBatchOutputPMF (inputOfKeyPair pair) none ^ totalRounds := by
  rw [branch_successMass_eq, NativeFiniteRetry.run_successProbability]

/-- Exact key-averaged success weights each original key's own conditional retry probability. -/
theorem successMass_eq :
    successMass base noQuantum bitWidth nonempty totalRounds inputs =
      ∑' pair, RSA.RSAKeyGenBits bitWidth nonempty pair *
        (1 - sampledBatchOutputPMF (inputOfKeyPair pair) none ^ totalRounds) := by
  rw [successMass, outputDistribution, PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro pair
  rw [branch_successProbability]

/-- Exact failure averages retry powers after fixing each original key, including zero rounds. -/
theorem failureMass_eq :
    failureMass base noQuantum bitWidth nonempty totalRounds inputs =
      ∑' pair, RSA.RSAKeyGenBits bitWidth nonempty pair *
        sampledBatchOutputPMF (inputOfKeyPair pair) none ^ totalRounds := by
  rw [failureMass, outputDistribution, PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro pair
  apply congrArg (fun mass => RSA.RSAKeyGenBits bitWidth nonempty pair * mass)
  rw [PMF.toOuterMeasure_map_apply]
  change
    ((NativeFiniteRetry.run base noQuantum (inputOfKeyPair pair) totalRounds).outputDistribution
      (inputs pair)).toOuterMeasure (NativeRetrySelection.decodeFactor ⁻¹' {none}) = _
  rw [← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton,
    NativeFiniteRetry.run_decoded_none]

/-- Original one-time analytic bound on the exceptional uniform key mass. -/
def keyFailureBound (bitWidth : Nat) : ENNReal :=
  ENNReal.ofReal (RSA.GeneratorOrder.keyFailureBound bitWidth)

/-- The unchanged uniform generator's nonexceptional mass has the original analytic floor. -/
theorem goodKeyMass_ge (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth) :
    1 - keyFailureBound bitWidth ≤
      (RSA.RSAKeyGenBits bitWidth nonempty).toOuterMeasure
        {pair | ¬ 2 ^ RSA.GeneratorOrder.gcdLossBits bitWidth ≤
          Nat.gcd (pair.p - 1) (pair.q - 1)} := by
  rw [PMF.eventProbability_eq_one_sub_complement]
  simp only [not_not]
  rw [RSA.GeneratorOrder.RSAKeyGenBits_commonDivisorBadMass_eq]
  exact tsub_le_tsub_left (ENNReal.ofReal_le_ofReal
    (RSA.GeneratorOrder.keyGenerationBadFraction_le_keyFailureBound effective)) 1

/-- Key-averaged actual success charges the key exception once outside the finite retry power. -/
theorem success_ge_rounds
    (effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth) :
    1 - (keyFailureBound bitWidth +
      NativeFiniteRetry.Calibration.batchFailure bitWidth ^ totalRounds) ≤
      successMass base noQuantum bitWidth nonempty totalRounds inputs := by
  let exceptional : RSA.RSAKeyPairBits bitWidth → Prop := fun pair =>
    2 ^ RSA.GeneratorOrder.gcdLossBits bitWidth ≤ Nat.gcd (pair.p - 1) (pair.q - 1)
  have bindLower :
      (RSA.RSAKeyGenBits bitWidth nonempty).toOuterMeasure {pair | ¬ exceptional pair} *
        (1 - NativeFiniteRetry.Calibration.batchFailure bitWidth ^ totalRounds) ≤
      successMass base noQuantum bitWidth nonempty totalRounds inputs := by
    unfold successMass outputDistribution
    apply PMF.bind_eventProbability_ge_goodMass_mul
      (exceptional := exceptional) (event := fun triple => triple ∈ successEvent)
    intro pair pairGood
    change 1 - NativeFiniteRetry.Calibration.batchFailure bitWidth ^ totalRounds ≤
      (((NativeFiniteRetry.run base noQuantum (inputOfKeyPair pair) totalRounds).outputDistribution
        (inputs pair)).map
          (fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output))).toOuterMeasure
            successEvent
    rw [branch_successMass_eq]
    let model : GoodKeyModel pair.modulus :=
      ⟨bitWidth, pair, rfl, effective, Nat.lt_of_not_ge pairGood⟩
    simpa only [model, GoodKeyModel.input, inputOfKeyPair] using
      NativeFiniteRetry.run_successProbability_ge base noQuantum model totalRounds (inputs pair)
  calc
    1 - (keyFailureBound bitWidth +
        NativeFiniteRetry.Calibration.batchFailure bitWidth ^ totalRounds) ≤
      (1 - keyFailureBound bitWidth) *
        (1 - NativeFiniteRetry.Calibration.batchFailure bitWidth ^ totalRounds) :=
      PMF.one_sub_add_le_mul_one_sub _ _
    _ ≤ (RSA.RSAKeyGenBits bitWidth nonempty).toOuterMeasure {pair | ¬ exceptional pair} *
        (1 - NativeFiniteRetry.Calibration.batchFailure bitWidth ^ totalRounds) := by
      simpa only [mul_comm] using
        mul_le_mul_right (goodKeyMass_ge bitWidth nonempty effective)
          (1 - NativeFiniteRetry.Calibration.batchFailure bitWidth ^ totalRounds)
    _ ≤ successMass base noQuantum bitWidth nonempty totalRounds inputs := bindLower

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeKeyGeneration
