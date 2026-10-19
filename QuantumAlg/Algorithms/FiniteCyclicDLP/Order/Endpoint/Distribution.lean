/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch.Distribution
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Recovery
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Run
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Probability

/-!
# Output law of the all-positive-order finite-cyclic DLP endpoint

The actual recovery circuit reads the retained batch produced by the same
execution and writes its checked first-success value.  This module first
separates that deterministic tail from the batch distribution.  Supplying the
trace-derived independent batch law then gives the complete endpoint law.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderEndpoint

open Execution

noncomputable section

attribute [local instance] Classical.decEq

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Checked endpoint value associated with one vector of observed outcomes. -/
@[expose] public def recoveredOutcome (P : KnownOrderProblem G)
    (outcomes : List.Vector
      (TerminalZMeasure.Outcome (OrderExecution.sampleWidth P)) (sampleCount P)) :
    CShape.Value (.option (.unsignedWord (OrderPreparation.width P))) :=
  recoveredValue P (rawSamples P (sampleCount P) outcomes)

/-- Independent source outcomes followed by the actual checked recovery value. -/
@[expose] public def outputLaw (P : KnownOrderProblem G) :
    PMF (CShape.Value (.option (.unsignedWord (OrderPreparation.width P)))) :=
  (PMF.independentReplicateVector
    (OrderBornBridge.outcomePMF P (OrderExecution.canonicalExpansion P))
    (sampleCount P)).map (recoveredOutcome P)

omit [Fintype G] in
/-- The outcome projection is recovery applied to the decoded raw sample vector. -/
public lemma recoveredOutcome_eq (P : KnownOrderProblem G)
    (outcomes : List.Vector
      (TerminalZMeasure.Outcome (OrderExecution.sampleWidth P)) (sampleCount P)) :
    recoveredOutcome P outcomes =
      recoveredValue P (rawSamples P (sampleCount P) outcomes) :=
  rfl

/-- The independent endpoint law maps the replicated observation law through recovery. -/
public lemma outputLaw_eq (P : KnownOrderProblem G) :
    outputLaw P =
      (PMF.independentReplicateVector
        (OrderBornBridge.outcomePMF P (OrderExecution.canonicalExpansion P))
        (sampleCount P)).map (recoveredOutcome P) :=
  rfl

private lemma observed_pmf_congr {C D Value : Type}
    [Fintype C] [Fintype D] [Fintype Value] {R : Register}
    (first : ExecutionState C R) (second : ExecutionState D R)
    (firstNormalized : first.IsNormalized) (secondNormalized : second.IsNormalized)
    (firstRead : C → Value) (secondRead : D → Value)
    (equal : first.mapClassical firstRead = second.mapClassical secondRead) :
    (first.toPMF firstNormalized).map firstRead =
      (second.toPMF secondNormalized).map secondRead := by
  have mapped : (first.mapClassical firstRead).toPMF
        (first.mapClassical_normalized firstNormalized firstRead) =
      (second.mapClassical secondRead).toPMF
        (second.mapClassical_normalized secondNormalized secondRead) := by
    apply PMF.ext
    intro value
    exact congrArg (fun state : ExecutionState Value R =>
      ENNReal.ofReal (state.block value).mass) equal
  exact (ExecutionState.toPMF_mapClassical first firstNormalized firstRead).symm.trans
    (mapped.trans (ExecutionState.toPMF_mapClassical second secondNormalized secondRead))

private lemma sequence_read {model : ExecutionModel}
    {environment : model.Environment}
    {pre middle post : RuntimeCtx model.kind}
    (first : Circuit model pre middle) (second : Circuit model middle post)
    {Reference : Register} {History Value : Type} [Fintype History] [Fintype Value]
    (state : State pre Reference (model.HiddenState × History))
    (read : Store post → Value) :
    ((first.seq second).execute environment Reference state).mapClassical
        (fun entry => read entry.1) =
      (second.execute environment Reference
        (first.execute environment Reference state)).mapClassical
        (fun entry => read entry.1) := by
  have executed := congrArg
    (fun output : State post Reference
      (model.HiddenState × (History × (first.seq second).Path)) =>
        output.mapClassical (fun entry => read entry.1))
    (Circuit.execute_seq (environment := environment) first second state)
  refine executed.trans ?_
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]

/-- The final cell of the actual complete circuit is the pure recovery value
of the retained raw batch produced by its sampling prefix. -/
public lemma code_observed (P : KnownOrderProblem G)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State OrderExecution.pre Reference
      ((OrderExecution.model P).HiddenState × History)) :
    ((code P).execute (OrderExecution.sourceEnvironment P) Reference state).mapClassical
        (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef)) =
      (retainedState P
        ((OrderBatch.code P (sampleCount P)
          (OrderExecution.canonicalExpansion P)).execute
            (OrderExecution.sourceEnvironment P) Reference state)).mapClassical
            (fun entry => recoveredValue P
              (.fixedVector fun index => entry.1.read (retainedSample P index))) := by
  let sampler := OrderBatch.code P (sampleCount P) (OrderExecution.canonicalExpansion P)
  let sampled := sampler.execute (OrderExecution.sourceEnvironment P) Reference state
  have sequenced := sequence_read
    (environment := OrderExecution.sourceEnvironment P) sampler (retainedRecovery P) state
    (fun store => store.read (.storage (outputRef P).toCStorageRef))
  exact sequenced.trans (retainedRecovery_read P sampled)

private lemma code_observed_probability (P : KnownOrderProblem G)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State OrderExecution.pre Reference
      ((OrderExecution.model P).HiddenState × History))
    (normalized : state.IsNormalized) :
    ((((code P).execute (OrderExecution.sourceEnvironment P) Reference state).toPMF
      (((code P).execute_mass
        (OrderExecution.sourceEnvironment P) Reference state).trans normalized)).map
        (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef))) =
      (((OrderBatch.code P (sampleCount P)
        (OrderExecution.canonicalExpansion P)).execute
          (OrderExecution.sourceEnvironment P) Reference state).toPMF
          (((OrderBatch.code P (sampleCount P)
            (OrderExecution.canonicalExpansion P)).execute_mass
              (OrderExecution.sourceEnvironment P) Reference state).trans
              normalized)).map
        (fun entry => recoveredValue P
          (entry.1.read (OrderBatch.samplesInput P (sampleCount P)))) := by
  let sampler := OrderBatch.code P (sampleCount P)
    (OrderExecution.canonicalExpansion P)
  let sampled := sampler.execute (OrderExecution.sourceEnvironment P) Reference state
  let retainedRead := fun entry : Store (outputContext P) ×
      ((OrderExecution.model P).HiddenState ×
        ((History × sampler.Path) × (outputAllocation P).Path)) =>
    recoveredValue P
      (.fixedVector fun index => entry.1.read (retainedSample P index))
  let sampledRead := fun entry : Store (sampledContext P) ×
      ((OrderExecution.model P).HiddenState × (History × sampler.Path)) =>
    recoveredValue P (entry.1.read (OrderBatch.samplesInput P (sampleCount P)))
  have sampledNormalized : sampled.IsNormalized :=
    (sampler.execute_mass (OrderExecution.sourceEnvironment P) Reference state).trans normalized
  have retainedNormalized : (retainedState P sampled).IsNormalized :=
    retainedState_normalized P sampled sampledNormalized
  have observed := observed_pmf_congr ((code P).execute
    (OrderExecution.sourceEnvironment P) Reference state)
    (retainedState P sampled)
    (((code P).execute_mass (OrderExecution.sourceEnvironment P) Reference state).trans normalized)
    retainedNormalized
    (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef))
    retainedRead
    (code_observed P state)
  refine observed.trans ?_
  have readPreserved : retainedRead ∘ retainedEntry P = sampledRead := by
    funext entry
    apply congrArg (recoveredValue P)
    rw [OrderBatch.samplesInput]
    change CShape.Value.fixedVector (fun index =>
        (retainedEntry P entry).1.read (retainedSample P index)) =
      CShape.Value.fixedVector (fun index => entry.1.read (OrderBatch.sampleInput P index))
    apply congrArg CShape.Value.fixedVector
    funext index
    exact retainedEntry_read_sample P entry index
  change ((retainedState P sampled).toPMF retainedNormalized).map retainedRead =
    (sampled.toPMF sampledNormalized).map sampledRead
  rw [retainedState_toPMF P sampled sampledNormalized, PMF.map_comp, readPreserved]

/-- Before using independence, the endpoint distribution is exactly the raw
batch distribution mapped through its actual deterministic recovery tail. -/
public lemma run_outputDistribution_raw (P : KnownOrderProblem G)
    {Reference : Register}
    (input : OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    (run P).outputDistribution (OrderExecution.sourceEnvironment P) input =
      ((OrderBatch.run P (sampleCount P)
        (OrderExecution.canonicalExpansion P)).outputDistribution
          (OrderExecution.sourceEnvironment P) input).map
          (recoveredValue P) := by
  let entered : State OrderExecution.pre Reference
      ((OrderExecution.model P).HiddenState × Store OrderExecution.pre) :=
    input.state.mapClassical (fun value => (value.1, (value.2, value.1)))
  have normalized := input.state.mapClassical_normalized input.normalized
    (fun value => (value.1, (value.2, value.1)))
  have actual := code_observed_probability P entered normalized
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.executionDistribution, PMF.map_comp]
  change ((((code P).execute (OrderExecution.sourceEnvironment P) Reference entered).toPMF
      (((code P).execute_mass
        (OrderExecution.sourceEnvironment P) Reference entered).trans normalized)).map
        (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef))) =
    (((OrderBatch.code P (sampleCount P)
      (OrderExecution.canonicalExpansion P)).execute
        (OrderExecution.sourceEnvironment P) Reference entered).toPMF
        (((OrderBatch.code P (sampleCount P)
          (OrderExecution.canonicalExpansion P)).execute_mass
            (OrderExecution.sourceEnvironment P) Reference entered).trans
            normalized)).map
      (fun entry => recoveredValue P
        (entry.1.read (OrderBatch.samplesInput P (sampleCount P))))
  exact actual

/-- Any trace-derived independent law for the actual batch closes the complete
endpoint law without an additional sampling or recovery assumption. -/
public lemma run_outputDistribution_of_batch (P : KnownOrderProblem G)
    {Reference : Register}
    (input : OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference)
    (batchLaw :
      ((OrderBatch.run P (sampleCount P)
        (OrderExecution.canonicalExpansion P)).outputDistribution
          (OrderExecution.sourceEnvironment P) input).map
          (OrderBatch.observedVector P (sampleCount P)) =
        PMF.independentReplicateVector
          (OrderBornBridge.outcomePMF P (OrderExecution.canonicalExpansion P))
          (sampleCount P)) :
    (run P).outputDistribution (OrderExecution.sourceEnvironment P) input = outputLaw P := by
  rw [run_outputDistribution_raw]
  let raw := (OrderBatch.run P (sampleCount P)
    (OrderExecution.canonicalExpansion P)).outputDistribution
      (OrderExecution.sourceEnvironment P) input
  have recoveryFactor :
      recoveredValue P = recoveredOutcome P ∘
        OrderBatch.observedVector P (sampleCount P) := by
    funext samples
    change recoveredValue P samples = recoveredValue P
      (rawSamples P (sampleCount P)
        (OrderBatch.observedVector P (sampleCount P) samples))
    rw [rawSamples_observed]
  rw [recoveryFactor, ← PMF.map_comp, batchLaw]
  rfl

/-- The complete endpoint run has its advertised output law from the actual
fresh-bank execution, terminal measurements and checked recovery circuit. -/
public lemma run_outputDistribution (P : KnownOrderProblem G)
    {Reference : Register}
    (input : OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    (run P).outputDistribution (OrderExecution.sourceEnvironment P) input = outputLaw P := by
  exact run_outputDistribution_of_batch P input
    (OrderBatch.run_outputDistribution P (sampleCount P)
      (OrderExecution.canonicalExpansion P) input)

end

end QuantumAlg.FiniteCyclicDLP.OrderEndpoint
