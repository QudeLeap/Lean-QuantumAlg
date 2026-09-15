/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Finite
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Probability
import all
  QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Soundness

/-!
# Actual finite oracle retry probabilities and checked factor outputs

The actual empty allocation supplies the zero-count law. Positive counts
use the already proved complete-reference law of the original fixed bank.
Every supported populated output is one original checked batch factor;
its canonical word fits the original modulus input without truncation.
The original good-key condition is needed only for the numerical success
floor, not for the run, distribution identity or factor soundness.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry.Finite

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Every total count has the original first-success law, including the actual empty run. -/
theorem nativeOracle_finiteRetry_outputDistribution (input : Input N) (totalRounds : Nat)
    {Reference : Register} (original : Execution.Input base Reference) :
    (run base noQuantum N input totalRounds).outputDistribution original =
      Optional.Distribution.selectedDistribution
        ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
        totalRounds := by
  cases totalRounds with
  | zero =>
      change (NativeRetryEmpty.run base N).outputDistribution original = _
      rw [NativeRetryEmpty.run_outputDistribution]
      simp only [Optional.Distribution.selectedDistribution, PMF.independentReplicateVector,
        PMF.pure_map, Optional.Distribution.firstValue, List.Vector.toList_nil, List.foldl_nil]
  | succ laterCount =>
      exact nativeOracle_retry_outputDistribution base noQuantum N input laterCount original

/-- Actual failure is exactly the original one-batch failure to the total number of batches. -/
theorem nativeOracle_finiteRetry_none (input : Input N) (totalRounds : Nat)
    {Reference : Register} (original : Execution.Input base Reference) :
    (run base noQuantum N input totalRounds).outputDistribution original .optionNone =
      sampledBatchOutputPMF input none ^ totalRounds := by
  rw [nativeOracle_finiteRetry_outputDistribution,
    Optional.Distribution.selectedDistribution_none, NativeRetrySelection.batch_outputValue_none]

/-- Populated actual outputs have the exact complementary success probability. -/
theorem nativeOracle_finiteRetry_successProbability (input : Input N) (totalRounds : Nat)
    {Reference : Register} (original : Execution.Input base Reference) :
    ((run base noQuantum N input totalRounds).outputDistribution original).toOuterMeasure
        {value | value ≠ CShape.Value.optionNone} =
      1 - sampledBatchOutputPMF input none ^ totalRounds := by
  rw [PMF.eventProbability_eq_one_sub_complement]
  have complement : {value : (LatticeBatchRecoveryOutput.OutputShape N).Value |
      ¬ value ≠ CShape.Value.optionNone} = {CShape.Value.optionNone} := by
    ext value
    simp only [not_not, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  rw [complement, PMF.toOuterMeasure_apply_singleton, nativeOracle_finiteRetry_none]

/-- Every supported populated actual word is a nontrivial divisor of the original modulus. -/
theorem nativeOracle_finiteRetry_some_sound (input : Input N) (totalRounds : Nat)
    {Reference : Register} (original : Execution.Input base Reference)
    (word : CShape.Word (modulusBits N))
    (supported : CShape.Value.optionSome word ∈
      ((run base noQuantum N input totalRounds).outputDistribution original).support) :
    word.toNat ∣ N ∧ 1 < word.toNat ∧ word.toNat < N := by
  rw [nativeOracle_finiteRetry_outputDistribution] at supported
  exact NativeRetrySelection.batch_outputValue_some_sound input word
    (Optional.Distribution.selectedDistribution_some_support _ totalRounds word supported)

/-- The original good-key floor bounds actual failure for every total batch count. -/
theorem nativeOracle_finiteRetry_none_le (model : GoodKeyModel N) (totalRounds : Nat)
    {Reference : Register} (original : Execution.Input base Reference) :
    (run base noQuantum N model.input totalRounds).outputDistribution original .optionNone ≤
      (1 - NativeBatchSuccess.successFloor model.bitWidth) ^ totalRounds := by
  rw [nativeOracle_finiteRetry_none]
  exact pow_le_pow_left' (NativeBatchSuccess.sampled_none_le model) totalRounds

/-- Only the original good-key domain is needed for the finite actual success guarantee. -/
theorem nativeOracle_finiteRetry_successProbability_ge (model : GoodKeyModel N)
    (totalRounds : Nat) {Reference : Register} (original : Execution.Input base Reference) :
    1 - (1 - NativeBatchSuccess.successFloor model.bitWidth) ^ totalRounds ≤
      ((run base noQuantum N model.input totalRounds).outputDistribution original).toOuterMeasure
        {value | value ≠ CShape.Value.optionNone} := by
  rw [nativeOracle_finiteRetry_successProbability]
  exact tsub_le_tsub_left
    (pow_le_pow_left' (NativeBatchSuccess.sampled_none_le model) totalRounds) 1

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry.Finite
