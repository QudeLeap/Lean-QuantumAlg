/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Distribution
import all QuantumAlg.Util.PMF
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Probability.Output
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Probability.Recovery
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.State
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Borrowed
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Events
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Space
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.QuantumTime
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Sampled
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Specification
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Soundness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Probability
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Distribution

/-!
# Complete contracts for the actual single-control RSA parent

The executable candidate contains exactly the new chronological run. The
original sampled-batch PMF enters through its proved actual output kernel;
no old full-bank execution theorem certifies this candidate. Complete joint
state, mandatory borrowed restoration and all independent native resource
coordinates belong to the same run. No kernel or seed premise is added to
the independent problem or the complete contract.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.Program

noncomputable section

variable {environment : ShortDLP.CompiledMAU.Recycling.model.Environment}

open Execution
open EkeraHastadStyle.Canonical
open ClassicalRoutines.FirstAccepted.Direct

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The sole execution source is the actual single-control chronological parent. -/
def algorithm (input : Input N) (count : Nat) :
    Algorithm ShortDLP.CompiledMAU.Recycling.model base
      (outputContext base noQuantum N count) (LatticeBatchRecoveryOutput.OutputShape N) where
  run := run base noQuantum N input count

/-- Actual trace-derived output probabilities equal the original finite first-success law. -/
lemma rsaRecyclingParent_run_outputDistribution (specification : Input N) (count : Nat)
    {Reference : Register}
    (input : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference) :
    (run base noQuantum N specification count).outputDistribution environment input =
      Probability.outputDistribution specification count :=
  Probability.run_outputPMF base noQuantum N specification count input.state input.normalized

/-- The actual empty-output probability is exactly the original batch failure to the count. -/
lemma rsaRecyclingParent_run_none (specification : Input N) (count : Nat)
    {Reference : Register}
    (input : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference) :
    (run base noQuantum N specification count).outputDistribution environment input
      CShape.Value.optionNone =
      sampledBatchOutputPMF specification none ^ count := by
  rw [rsaRecyclingParent_run_outputDistribution, Probability.outputDistribution,
    Optional.Distribution.selectedDistribution_none]
  exact congrArg (fun probability : ENNReal => probability ^ count)
    (NativeRetrySelection.batch_outputValue_none specification)

/-- Populated actual output has the exact complementary success probability, also at zero. -/
lemma rsaRecyclingParent_run_successProbability (specification : Input N) (count : Nat)
    {Reference : Register}
    (input : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference) :
    ((run base noQuantum N specification count).outputDistribution environment input).toOuterMeasure
        {value | value ≠ CShape.Value.optionNone} =
      1 - sampledBatchOutputPMF specification none ^ count := by
  rw [PMF.eventProbability_eq_one_sub_complement]
  have complement : {value : (LatticeBatchRecoveryOutput.OutputShape N).Value |
      ¬ value ≠ CShape.Value.optionNone} = {CShape.Value.optionNone} := by
    ext value
    simp only [not_not, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  rw [complement, PMF.toOuterMeasure_apply_singleton, rsaRecyclingParent_run_none]

/-- Actual populated output is a checked nontrivial divisor for every original modulus input. -/
lemma rsaRecyclingParent_run_some_sound (specification : Input N) (count : Nat)
    {Reference : Register}
    (input : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference)
    (word : CShape.Word (modulusBits N))
    (supported : CShape.Value.optionSome word ∈
      ((run base noQuantum N specification count).outputDistribution environment input).support) :
    word.toNat ∣ N ∧ 1 < word.toNat ∧ word.toNat < N := by
  rw [rsaRecyclingParent_run_outputDistribution, Probability.outputDistribution] at supported
  exact NativeRetrySelection.batch_outputValue_some_sound specification word
    (Optional.Distribution.selectedDistribution_some_support _ count word supported)

/-- The original conditional floor bounds the actual finite-run success, with no caller premise. -/
lemma rsaRecyclingParent_run_successProbability_ge (key : GoodKeyModel N) (count : Nat)
    {Reference : Register}
    (input : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference) :
    1 - NativeFiniteRetry.Calibration.batchFailure key.bitWidth ^ count ≤
      ((run base noQuantum N key.input count).outputDistribution environment input).toOuterMeasure
        {value | value ≠ CShape.Value.optionNone} := by
  rw [rsaRecyclingParent_run_successProbability]
  exact tsub_le_tsub_left
    (pow_le_pow_left' (NativeBatchSuccess.sampled_none_le key) count) 1

/-- The exact real calibration reserves half the target for original exceptional-key loss. -/
lemma rsaRecyclingParent_run_successProbability_ge_halfTarget (key : GoodKeyModel N)
    (η : Real) (positive : 0 < η) {Reference : Register}
    (input : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference) :
    1 - ENNReal.ofReal (η / 2) ≤
      ((run base noQuantum N key.input
        (NativeFiniteRetry.Calibration.retryCount η)).outputDistribution environment
          input).toOuterMeasure
          {value | value ≠ CShape.Value.optionNone} :=
  (tsub_le_tsub_left
    (NativeFiniteRetry.Calibration.retryBatchFailure_le_halfTarget key.effective η positive)
    1).trans (rsaRecyclingParent_run_successProbability_ge base noQuantum key _ input)

/-- Complete state restoration now has no internal kernel premise left to discharge. -/
lemma rsaRecyclingParent_stateRequirement_holds (specification : Input N) (count : Nat)
    {Reference : Register}
    (input : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference) :
    (stateRequirement base noQuantum N count).Holds input.caller
      ((run base noQuantum N specification count).finalState environment Reference input.state) :=
  rsaRecyclingParent_stateRequirement_of_kernel base noQuantum N specification count
    (Probability.outputDistribution specification count)
    (Probability.referenceKernel_output base noQuantum N specification count) input

/-- Complete independent finite-count problem for the new physical execution. -/
def fixedRoundProblem (N count : Nat) :
    Problem ShortDLP.CompiledMAU.Recycling.model base
      (outputContext base noQuantum N count) (LatticeBatchRecoveryOutput.OutputShape N) where
  Witness := GoodKeyModel N
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun _ key _ output => NativeRetrySelection.decodeFactor output ∈
    NativeBatchSuccess.accepts key
  successLB := fun _ key => ⟨1 - NativeFiniteRetry.Calibration.batchFailure key.bitWidth ^ count,
    tsub_le_self⟩
  states := fun _ _ => [stateRequirement base noQuantum N count]
  resources :=
    { events := eventBudget N count
      resident := base.residentSpace + spaceLimit N count
      auxiliary := base.auxiliarySpace + spaceLimit N count }
  quantumTimeLimit := quantumTimeLimit N count

private lemma accepts_probability (key : GoodKeyModel N) (count : Nat)
    {Reference : Register}
    (input : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference) :
    ((run base noQuantum N key.input count).outputDistribution environment input).toOuterMeasure
        {output | NativeRetrySelection.decodeFactor output ∈ NativeBatchSuccess.accepts key} =
      ((run base noQuantum N key.input count).outputDistribution environment input).toOuterMeasure
        {output | output ≠ CShape.Value.optionNone} := by
  apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
  ext output
  simp only [Set.mem_inter_iff]
  apply and_congr_left
  intro supported
  cases output with
  | optionNone =>
      change none ∈ NativeBatchSuccess.accepts key ↔
        (CShape.Value.optionNone : (LatticeBatchRecoveryOutput.OutputShape N).Value) ≠ .optionNone
      simp only [NativeBatchSuccess.not_accepts_none, ne_eq, not_true_eq_false]
  | optionSome word =>
      have sound := rsaRecyclingParent_run_some_sound base noQuantum key.input count
        input word supported
      have declared := key.semiprime.nontrivial_factor_eq_declared sound.1 sound.2.1 sound.2.2
      exact iff_of_true ((NativeBatchSuccess.accepts_some key).mpr declared)
        (by intro impossible; cases impossible)

/-- Relational acceptance observes the same original input and the actual stored factor. -/
lemma rsaRecyclingParent_relational_probability (key : GoodKeyModel N) (count : Nat)
    {Reference : Register}
    (input : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference) :
    ((algorithm base noQuantum key.input count).relationalDistribution environment
      input).toOuterMeasure
        {pair | (fixedRoundProblem base noQuantum N count).accepts environment key pair.1 pair.2} =
      ((run base noQuantum N key.input count).outputDistribution environment input).toOuterMeasure
        {output | output ≠ CShape.Value.optionNone} := by
  have projection :
      ((algorithm base noQuantum key.input count).relationalDistribution environment
        input).toOuterMeasure
          {pair | (fixedRoundProblem base noQuantum N count).accepts environment key pair.1
            pair.2} =
        ((run base noQuantum N key.input count).outputDistribution environment input).toOuterMeasure
          {output | NativeRetrySelection.decodeFactor output ∈ NativeBatchSuccess.accepts key} := by
    simp only [Algorithm.relationalDistribution, algorithm, AlgorithmRun.relationalDistribution,
      AlgorithmRun.outputDistribution, PMF.toOuterMeasure_map_apply]
    rfl
  exact projection.trans (accepts_probability base noQuantum key count input)

/-- One actual algorithm meets all seven gates with independent budgets and no kernel premise. -/
lemma rsaRecyclingParent_algorithm_solves_fixedRound (specification : Input N) (count : Nat) :
    (algorithm base noQuantum specification count).Solves
      (fixedRoundProblem base noQuantum N count) := by
  constructor
  · intro environment key Reference input _valid _initialized
    rw [rsaRecyclingParent_relational_probability (environment := environment)
      base noQuantum key count input]
    exact rsaRecyclingParent_run_successProbability_ge base noQuantum key count input
  · intro environment key Reference input _valid _initialized requirement present
    have same : requirement = stateRequirement base noQuantum N count :=
      List.mem_singleton.mp present
    subst requirement
    exact rsaRecyclingParent_stateRequirement_holds base noQuantum specification count input
  · intro environment key Reference input _valid _initialized
    exact rsaRecyclingParent_restoresBorrowed base noQuantum N specification count input
  · intro _environment _key _Reference _input _valid _initialized path _supported
    exact rsaRecyclingParent_run_pool_le base noQuantum N specification count path
  · intro _environment _key _Reference _input _valid _initialized path _supported
    exact rsaRecyclingParent_run_resident_le base noQuantum N specification count path
  · intro _environment _key _Reference _input _valid _initialized path _supported
    exact rsaRecyclingParent_run_auxiliary_le base noQuantum N specification count path
  · intro _environment _key _Reference _input _valid _initialized path _supported
    exact rsaRecyclingParent_run_quantumTime_le base noQuantum N specification count path

end

end QuantumAlg.Factoring.RSA.Recycling.Program
