/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Probability
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Sampled

/-!
# Conditional success of the actual finite retry run

The original shared-source batch floor bounds the exact empty-output power
of the actual finite run. The original rational calibration then bounds its
retry failure by half of the caller's target. Good-key data enter only these
probability proofs; the executable input remains the original modulus input.
Key-generation exceptions are accounted for separately, outside this power.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry

noncomputable section

open ShortDLP.CompiledMAU

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Actual empty-output mass is bounded by the original conditional batch-failure power. -/
theorem run_none_le_batchFailure (model : GoodKeyModel N) (totalRounds : Nat)
    {Reference : Register}
    (input : Execution.OracleInput RuntimeRound.model.classicalOracles base Reference) :
    (run base noQuantum model.input totalRounds).outputDistribution input
        CShape.Value.optionNone ≤ Calibration.batchFailure model.bitWidth ^ totalRounds := by
  rw [run_none]
  exact pow_le_pow_left' (NativeBatchSuccess.sampled_none_le model) totalRounds

/-- The actual populated-output event has the original finite conditional success floor. -/
theorem run_successProbability_ge (model : GoodKeyModel N) (totalRounds : Nat)
    {Reference : Register}
    (input : Execution.OracleInput RuntimeRound.model.classicalOracles base Reference) :
    1 - Calibration.batchFailure model.bitWidth ^ totalRounds ≤
      ((run base noQuantum model.input totalRounds).outputDistribution input).toOuterMeasure
        {value | value ≠ CShape.Value.optionNone} := by
  rw [run_successProbability]
  exact tsub_le_tsub_left
    (pow_le_pow_left' (NativeBatchSuccess.sampled_none_le model) totalRounds) 1

/-- Natural observation preserves the conditional actual empty-output bound. -/
theorem run_decoded_none_le_batchFailure (model : GoodKeyModel N) (totalRounds : Nat)
    {Reference : Register}
    (input : Execution.OracleInput RuntimeRound.model.classicalOracles base Reference) :
    ((run base noQuantum model.input totalRounds).outputDistribution input).map
        NativeRetrySelection.decodeFactor none ≤
      Calibration.batchFailure model.bitWidth ^ totalRounds := by
  rw [run_decoded_none]
  exact pow_le_pow_left' (NativeBatchSuccess.sampled_none_le model) totalRounds

/-- The exact calibrated actual run spends at most half of the declared failure target. -/
theorem run_none_le_halfTarget (model : GoodKeyModel N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed)
    {Reference : Register}
    (input : Execution.OracleInput RuntimeRound.model.classicalOracles base Reference) :
    (run base noQuantum model.input (Calibration.retryCount budget)).outputDistribution input
        CShape.Value.optionNone ≤ ENNReal.ofReal (budget.value / 2) :=
  (run_none_le_batchFailure base noQuantum model _ input).trans
    (Calibration.retryBatchFailure_le_halfTarget model.effective budget wellFormed)

/-- Conditional success of the calibrated actual run reserves half the target for key loss. -/
theorem run_successProbability_ge_halfTarget (model : GoodKeyModel N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed)
    {Reference : Register}
    (input : Execution.OracleInput RuntimeRound.model.classicalOracles base Reference) :
    1 - ENNReal.ofReal (budget.value / 2) ≤
      ((run base noQuantum model.input (Calibration.retryCount budget)).outputDistribution
        input).toOuterMeasure {value | value ≠ CShape.Value.optionNone} :=
  (tsub_le_tsub_left
    (Calibration.retryBatchFailure_le_halfTarget model.effective budget wellFormed) 1).trans
      (run_successProbability_ge base noQuantum model _ input)

/-- Natural decoding also retains the calibrated actual empty-output guarantee. -/
theorem run_decoded_none_le_halfTarget (model : GoodKeyModel N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed)
    {Reference : Register}
    (input : Execution.OracleInput RuntimeRound.model.classicalOracles base Reference) :
    ((run base noQuantum model.input (Calibration.retryCount budget)).outputDistribution
        input).map NativeRetrySelection.decodeFactor none ≤ ENNReal.ofReal (budget.value / 2) :=
  (run_decoded_none_le_batchFailure base noQuantum model _ input).trans
    (Calibration.retryBatchFailure_le_halfTarget model.effective budget wellFormed)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry
