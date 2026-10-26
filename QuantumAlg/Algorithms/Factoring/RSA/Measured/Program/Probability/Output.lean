/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Probability.Retry
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Kernel.Positive
import all QuantumAlg.Core.Execution.Reference.Probability
import all QuantumAlg.Util.PMF.FiniteWeights

/-!
# The original finite-retry distribution of the actual measured RSA output

The complete actual parent/reference kernel is reduced to the unchanged
first-populated distribution only after source, members, all-pairs recovery
and final selection have been composed. The physical program, retained
Store and both external Reference coordinates are unchanged
[EH17, source.tex:878-966; G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program.Probability

noncomputable section

variable [configuration : Configuration]

open Execution ClassicalRoutines EkeraHastadStyle.Canonical
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

/-- Original chronological first-success distribution at every natural retry count. -/
def outputDistribution {N : Nat} (input : Input N) (count : Nat) : PMF (Factor N) :=
  FirstAccepted.Direct.Optional.Distribution.selectedDistribution (batchDistribution input) count

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The real bank output reads the same retained complete parent selected-factor cell. -/
lemma rsaMeasuredProbability_positiveRun_output (input : Input N) (laterCount : Nat)
    (stored : Store (readyContext base noQuantum N (laterCount + 1))) :
    (positiveRun base noQuantum N input laterCount).output.eval stored =
      selectedRead base N (laterCount + 1)
        (parentStoreAt base noQuantum N (laterCount + 1) stored) :=
  (ShortDLP.CompiledMAU.Recycling.Measured.parentTransport
    (Recycling.ClassicalFrame.context base N (laterCount + 1))
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).workspaceTransport_restrict_readsAs
    stored (FirstAccepted.cellRead (Recycling.ClassicalFrame.selectedRef base N (laterCount + 1)))

/-- Arbitrary final factor weights of the actual positive parent kernel have the original law. -/
lemma rsaMeasuredProbability_positiveKernel_output (input : Input N) (laterCount : Nat)
    (weight : Factor N → ℂ) (original : Store base) :
    positiveParentReferenceKernel base N laterCount
        (fun stored => weight (selectedRead base N (laterCount + 1) stored)) original =
      ∑ output : Factor N,
        ((outputDistribution input (laterCount + 1) output).toReal : ℂ) * weight output := by
  let remaining : Factor N → ℂ := fun first =>
    ∑ values : List.Vector (Factor N) laterCount,
      ((PMF.independentReplicateVector (batchDistribution input) laterCount values).toReal : ℂ) *
        weight (FirstAccepted.Direct.Optional.Distribution.firstValue (first :: values.toList))
  have tail : laterBatchesParentReferenceKernel base N laterCount
      (fun stored => weight (selectedRead base N (laterCount + 1)
        (parentSelectionStore base N (laterCount + 1) stored))) =
      (fun stored => remaining (factorRead base N (laterCount + 1) stored 0)) := by
    funext stored
    exact rsaMeasuredProbability_laterBatches_selected base N input laterCount weight stored
  have firstMoment : positiveParentReferenceKernel base N laterCount
      (fun stored => weight (selectedRead base N (laterCount + 1) stored)) original =
      ∑ factor : Factor N, ((batchDistribution input factor).toReal : ℂ) * remaining factor := by
    rw [rsaMeasuredProbability_batchDistribution_weighted]
    unfold positiveParentReferenceKernel sourceParentReferenceKernel tailParentReferenceKernel
    rw [tail]
    apply Finset.sum_congr rfl
    intro sample _
    apply congrArg (fun value : ℂ => (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) * value)
    have actual := rsaMeasuredProbability_batchBody_factorKernel base N (laterCount + 1) input
      sample 0 (fun factors => remaining (factors 0))
      (sourceStore N (Recycling.ClassicalFrame.sampleRef base N (laterCount + 1) 0)
        (Recycling.ClassicalFrame.parameterRef base N (laterCount + 1) 0)
        (Recycling.ClassicalFrame.pushStore base N (laterCount + 1) original) sample)
      (rsaMeasuredParent_sourceStore_parameter N _ _ input _ sample)
      (rsaMeasuredProbability_sourceStore_sample base N (laterCount + 1) input 0 _ sample)
    simpa only [Function.update_self] using actual
  refine firstMoment.trans ?_
  have mapped := PMF.sum_map_toReal_mul
    (PMF.independentReplicateVector (batchDistribution input) (laterCount + 1))
    (fun values => FirstAccepted.Direct.Optional.Distribution.firstValue values.toList) weight
  have vector := PMF.independentReplicateVector_weighted_cons (batchDistribution input)
    laterCount (fun values => weight
      (FirstAccepted.Direct.Optional.Distribution.firstValue values.toList))
  exact (mapped.trans (by simpa only [List.Vector.toList_cons] using vector)).symm

/-- Actual positive execution has the original law for both coordinates of every Reference. -/
lemma rsaMeasuredProbability_positiveRun_output_reference (input : Input N) (laterCount : Nat)
    (environment : MeasuredRSAModel.Environment) {Reference : Register}
    (state : ExecutionState (Store base × MeasuredRSAModel.HiddenState)
      (Register.prod base.register Reference))
    (weight : Factor N → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((positiveRun base noQuantum N input laterCount).execute environment Reference state)
        (fun entry _ => weight
          ((positiveRun base noQuantum N input laterCount).output.eval entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ output : Factor N,
          ((outputDistribution input (laterCount + 1) output).toReal : ℂ) * weight output)
        left right := by
  let : NeZero (modulusWord N).toNat :=
    ⟨fun zero => input.neZero.out ((measuredRSA_modulusWord_toNat N).symm.trans zero)⟩
  have observation :
      (fun entry : (positiveRun base noQuantum N input laterCount).Record =>
        fun _basis : (readyContext base noQuantum N (laterCount + 1)).register.Index =>
          weight ((positiveRun base noQuantum N input laterCount).output.eval entry.1)) =
      (fun entry _ => weight (selectedRead base N (laterCount + 1)
        (parentStoreAt base noQuantum N (laterCount + 1) entry.1))) := by
    funext entry _basis
    exact congrArg weight
      (rsaMeasuredProbability_positiveRun_output base noQuantum N input laterCount entry.1)
  rw [observation]
  refine (rsaMeasuredParent_positiveCode_parent_referenceFiberSum base noQuantum N input
    laterCount environment
    (state.mapClassical (fun entry => (entry.1, (entry.2, entry.1))))
    (fun stored => weight (selectedRead base N (laterCount + 1) stored)) left right).trans ?_
  rw [ExecutionState.referenceFiberSum_mapClassical]
  apply congrArg (fun observed => ExecutionState.referenceFiberSum state observed left right)
  funext entry _basis
  exact rsaMeasuredProbability_positiveKernel_output base N input laterCount weight entry.1

/-- The actual positive trace-derived output PMF is precisely the original finite-retry PMF. -/
lemma rsaMeasuredProbability_positiveRun_outputPMF (input : Input N) (laterCount : Nat)
    (environment : MeasuredRSAModel.Environment) {Reference : Register}
    (state : ExecutionState (Store base × MeasuredRSAModel.HiddenState)
      (Register.prod base.register Reference)) (normalized : state.IsNormalized) :
    (((positiveRun base noQuantum N input laterCount).execute environment Reference state).toPMF
      (((positiveRun base noQuantum N input laterCount).execute_mass environment Reference
        state).trans normalized)).map
          (fun entry => (positiveRun base noQuantum N input laterCount).output.eval entry.1) =
      outputDistribution input (laterCount + 1) := by
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum state _ normalized
    (((positiveRun base noQuantum N input laterCount).execute_mass environment Reference
      state).trans normalized)
  intro selected left right
  exact (rsaMeasuredProbability_positiveRun_output_reference base noQuantum N input laterCount
    environment state (fun value => if value = selected then 1 else 0) left right).trans
    (congrArg (fun coefficient : ℂ =>
      ExecutionState.referenceFiberSum state (fun _ _ => coefficient) left right)
      (PMF.sum_toReal_indicator (outputDistribution input (laterCount + 1)) selected))

/-- Every natural batch count uses that same actual output law, including the literal empty run. -/
lemma rsaMeasuredProbability_run_outputDistribution (input : Input N) (count : Nat)
    (environment : MeasuredRSAModel.Environment) {Reference : Register}
    (initial : OracleInput .empty base Reference) :
    (run base noQuantum N input count).outputDistribution environment initial =
      outputDistribution input count := by
  cases count with
  | zero =>
      refine (NativeRetryEmpty.run_outputDistribution (environment := environment)
        base N initial).trans ?_
      simp only [outputDistribution,
        FirstAccepted.Direct.Optional.Distribution.selectedDistribution,
        PMF.independentReplicateVector, PMF.pure_map,
        FirstAccepted.Direct.Optional.Distribution.firstValue, List.Vector.toList_nil,
        List.foldl_nil]
  | succ laterCount =>
      exact rsaMeasuredProbability_positiveRun_outputPMF base noQuantum N input laterCount
        environment initial.state initial.normalized

end

end QuantumAlg.Factoring.RSA.Measured.Program.Probability
