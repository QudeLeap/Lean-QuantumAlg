/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Specification
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration

/-!
# Declared-prime acceptance of the completed EH execution

The original good-key predicate accepts precisely the two declared primes.
The direct completed source law and its supported-factor soundness identify
that event on every actual output distribution, including count zero.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- On the completed run, the original declared-prime acceptance mass equals
the populated mass for every count and normalized caller/service/reference input. -/
theorem completedAlgorithm_primeAcceptance_eq_populated (good : GoodKeyModel N)
    (count : Nat) {Reference : Register}
    (original : Execution.OracleInput (model good.input).classicalOracles base Reference) :
    ((completedAlgorithm base noQuantum good.input count).run.outputDistribution
      original).toOuterMeasure
          {output | NativeRetrySelection.decodeFactor output ∈ NativeBatchSuccess.accepts good} =
      ((completedAlgorithm base noQuantum good.input count).run.outputDistribution
        original).toOuterMeasure {output | output ≠ CShape.Value.optionNone} := by
  apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
  ext output
  simp only [Set.mem_inter_iff]
  apply and_congr_left
  intro supported
  cases output with
  | optionNone =>
      change none ∈ NativeBatchSuccess.accepts good ↔
        (CShape.Value.optionNone : (LatticeBatchRecoveryOutput.OutputShape N).Value) ≠ .optionNone
      simp only [NativeBatchSuccess.not_accepts_none, ne_eq, not_true_eq_false]
  | optionSome word =>
      have sound := completedAlgorithm_some_sound base noQuantum good.input count
        original word supported
      have declared := good.semiprime.nontrivial_factor_eq_declared
        sound.1 sound.2.1 sound.2.2
      exact iff_of_true ((NativeBatchSuccess.accepts_some good).mpr declared)
        (by intro impossible; cases impossible)

/-- The same completed output meets the original good-key finite success floor
for the original declared-prime event, with zero included. -/
theorem completedAlgorithm_primeAcceptance_ge (good : GoodKeyModel N)
    (count : Nat) {Reference : Register}
    (original : Execution.OracleInput (model good.input).classicalOracles base Reference) :
    1 - (1 - NativeBatchSuccess.successFloor good.bitWidth) ^ count ≤
      ((completedAlgorithm base noQuantum good.input count).run.outputDistribution
        original).toOuterMeasure
        {output | NativeRetrySelection.decodeFactor output ∈ NativeBatchSuccess.accepts good} := by
  rw [completedAlgorithm_primeAcceptance_eq_populated]
  exact completedAlgorithm_successProbability_ge base noQuantum good count original

/-- Calibration retains the original conditional half-target for the declared
primes on this actual completed execution. -/
theorem completedAlgorithm_primeAcceptance_ge_halfTarget (good : GoodKeyModel N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) {Reference : Register}
    (original : Execution.OracleInput (model good.input).classicalOracles base Reference) :
    1 - ENNReal.ofReal (budget.value / 2) ≤
      ((completedAlgorithm base noQuantum good.input
        (calibratedCount budget)).run.outputDistribution original).toOuterMeasure
        {output | NativeRetrySelection.decodeFactor output ∈ NativeBatchSuccess.accepts good} := by
  exact (tsub_le_tsub_left
    (NativeFiniteRetry.Calibration.retryBatchFailure_le_halfTarget
      good.effective budget wellFormed) 1).trans
    (completedAlgorithm_primeAcceptance_ge base noQuantum good
      (calibratedCount budget) original)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
