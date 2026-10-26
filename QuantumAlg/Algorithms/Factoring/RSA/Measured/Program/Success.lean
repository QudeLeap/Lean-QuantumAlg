/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Probability.Output
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Count
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Specification
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Soundness
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Probability
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration
import all QuantumAlg.Util.PMF

/-!
# Soundness and original conditional success of the actual measured parent

The exact actual output PMF gives the original finite-retry failure power
and checked factor support, for every admitted original input, caller Store
and external Reference [EH17, source.tex:878-966].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]
variable {environment : MeasuredRSAModel.Environment}

open Execution EkeraHastadStyle.Canonical
open ClassicalRoutines.FirstAccepted.Direct

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The actual empty-output probability is exactly the original batch failure to the count. -/
lemma rsaMeasuredParent_run_none (specification : Input N) (count : Nat)
    {Reference : Register}
    (input : OracleInput MeasuredRSAModel.classicalOracles base Reference) :
    (run base noQuantum N specification count).outputDistribution environment input
      CShape.Value.optionNone =
      sampledBatchOutputPMFAtCount specification membersPerBatch none ^ count := by
  rw [Probability.rsaMeasuredProbability_run_outputDistribution, Probability.outputDistribution,
    Optional.Distribution.selectedDistribution_none]
  exact congrArg (fun probability : ENNReal => probability ^ count)
    (NativeRetrySelection.batch_outputValue_none_atCount specification)

/-- Populated actual output has the exact complementary success probability, also at zero. -/
lemma rsaMeasuredParent_run_successProbability (specification : Input N) (count : Nat)
    {Reference : Register}
    (input : OracleInput MeasuredRSAModel.classicalOracles base Reference) :
    ((run base noQuantum N specification count).outputDistribution environment input).toOuterMeasure
        {value | value ≠ CShape.Value.optionNone} =
      1 - sampledBatchOutputPMFAtCount specification membersPerBatch none ^ count := by
  rw [PMF.eventProbability_eq_one_sub_complement]
  have complement : {value : (LatticeBatchRecoveryOutput.OutputShape N).Value |
      ¬ value ≠ CShape.Value.optionNone} = {CShape.Value.optionNone} := by
    ext value
    simp only [not_not, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  rw [complement, PMF.toOuterMeasure_apply_singleton, rsaMeasuredParent_run_none]

/-- Actual populated output is a checked nontrivial divisor for every original modulus input. -/
lemma rsaMeasuredParent_run_some_sound (specification : Input N) (count : Nat)
    {Reference : Register}
    (input : OracleInput MeasuredRSAModel.classicalOracles base Reference)
    (word : CShape.Word (modulusBits N))
    (supported : CShape.Value.optionSome word ∈
      ((run base noQuantum N specification count).outputDistribution environment input).support) :
    word.toNat ∣ N ∧ 1 < word.toNat ∧ word.toNat < N := by
  rw [Probability.rsaMeasuredProbability_run_outputDistribution, Probability.outputDistribution]
    at supported
  exact NativeRetrySelection.batch_outputValue_some_sound_atCount specification word
    (Optional.Distribution.selectedDistribution_some_support _ count word supported)

/-- The original conditional floor bounds the actual finite-run success, with no caller premise. -/
lemma rsaMeasuredParent_run_successProbability_ge
    (specification : Input N) (key : GoodKeyModel N) (count : Nat)
    {Reference : Register}
    (input : OracleInput MeasuredRSAModel.classicalOracles base Reference) :
    1 - NativeFiniteRetry.Calibration.batchFailure key.bitWidth ^ count ≤
      ((run base noQuantum N specification count).outputDistribution environment
        input).toOuterMeasure
        {value | value ≠ CShape.Value.optionNone} := by
  rw [rsaMeasuredParent_run_successProbability]
  have sameFailure := congrArg
    (fun proof : Input N => sampledBatchOutputPMFAtCount proof membersPerBatch none)
    (Subsingleton.elim specification key.input)
  rw [sameFailure]
  exact tsub_le_tsub_left
    (pow_le_pow_left' (NativeBatchSuccess.sampled_none_le_of_count_ge key
      (by have original := configuration.originalMembers;
          unfold membersPerBatch; omega)) count) 1

/-- The exact real calibration reserves half the target for original exceptional-key loss. -/
lemma rsaMeasuredParent_run_successProbability_ge_halfTarget
    (specification : Input N) (key : GoodKeyModel N)
    (η : Real) (positive : 0 < η) {Reference : Register}
    (input : OracleInput MeasuredRSAModel.classicalOracles base Reference) :
    1 - ENNReal.ofReal (η / 2) ≤
      ((run base noQuantum N specification
        (NativeFiniteRetry.Calibration.retryCount η)).outputDistribution environment
          input).toOuterMeasure
          {value | value ≠ CShape.Value.optionNone} :=
  (tsub_le_tsub_left
    (NativeFiniteRetry.Calibration.retryBatchFailure_le_halfTarget key.effective η positive)
    1).trans
      (rsaMeasuredParent_run_successProbability_ge base noQuantum specification key _ input)

end

end QuantumAlg.Factoring.RSA.Measured.Program
