/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Samples
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Probability
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Distribution
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Recovery
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Context
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Program
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Run
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Probability

/-!
# Output composition for the actual sequential binary endpoint

The actual recovery circuit reads the retained batch produced by the same
execution and writes its checked first-success value.  This module first
separates that deterministic tail from the sample distribution. The separate reusable-bank
  proof supplies the
trace-derived independent law, including arbitrary hidden and reference states
[Sho95, source.tex:1784-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

open Execution

noncomputable section

attribute [local instance] Classical.decEq

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Checked endpoint value associated with one vector of observed outcomes. -/
@[expose] public def recoveredOutcome (P : KnownOrderProblem G)
    (outcomes : List.Vector
      (TerminalZMeasure.Outcome (Reusable.sampleWidth P)) (sampleCount P)) :
    CShape.Value (.option (.unsignedWord (OrderPreparation.width P))) :=
  recoveredValue P (rawSamples P (sampleCount P) outcomes)

/-- Independent source outcomes followed by the actual checked recovery value. -/
@[expose] public def outputLaw (P : KnownOrderProblem G) :
    PMF (CShape.Value (.option (.unsignedWord (OrderPreparation.width P)))) :=
  (PMF.independentReplicateVector
    (Binary.outcomePMF P (OrderExecution.canonicalExpansion P))
    (sampleCount P)).map (recoveredOutcome P)

omit [Fintype G] in
/-- The outcome projection is recovery applied to the decoded raw sample vector. -/
public lemma binaryEndpoint_recoveredOutcome_eq (P : KnownOrderProblem G)
    (outcomes : List.Vector
      (TerminalZMeasure.Outcome (Reusable.sampleWidth P)) (sampleCount P)) :
    recoveredOutcome P outcomes =
      recoveredValue P (rawSamples P (sampleCount P) outcomes) :=
  rfl

omit [Fintype G] in
/-- The independent endpoint law maps the replicated observation law through recovery. -/
public lemma binaryEndpoint_outputLaw_eq (P : KnownOrderProblem G) :
    outputLaw P =
      (PMF.independentReplicateVector
        (Binary.outcomePMF P (OrderExecution.canonicalExpansion P))
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
public lemma binaryEndpoint_code_observed (P : KnownOrderProblem G)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State Reusable.pre Reference
      ((Reusable.model P).HiddenState × History)) :
    ((code P).execute (Reusable.sourceEnvironment P) Reference state).mapClassical
        (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef)) =
      (retainedState P
        ((Reusable.code P (sampleCount P)
          (OrderExecution.canonicalExpansion P)).execute
            (Reusable.sourceEnvironment P) Reference state)).mapClassical
            (fun entry => recoveredValue P
              (.fixedVector fun index => entry.1.read (retainedSample P index))) := by
  let sampler := Reusable.code P (sampleCount P) (OrderExecution.canonicalExpansion P)
  let sampled := sampler.execute (Reusable.sourceEnvironment P) Reference state
  have sequenced := sequence_read
    (environment := Reusable.sourceEnvironment P) sampler (retainedRecovery P) state
    (fun store => store.read (.storage (outputRef P).toCStorageRef))
  exact sequenced.trans (binaryEndpoint_retainedRecovery_read P sampled)

private lemma code_observed_probability (P : KnownOrderProblem G)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State Reusable.pre Reference
      ((Reusable.model P).HiddenState × History))
    (normalized : state.IsNormalized) :
    ((((code P).execute (Reusable.sourceEnvironment P) Reference state).toPMF
      (((code P).execute_mass (Reusable.sourceEnvironment P) Reference state).trans normalized)).map
        (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef))) =
      (((Reusable.code P (sampleCount P)
        (OrderExecution.canonicalExpansion P)).execute
          (Reusable.sourceEnvironment P) Reference state).toPMF
          (((Reusable.code P (sampleCount P)
            (OrderExecution.canonicalExpansion P)).execute_mass
              (Reusable.sourceEnvironment P) Reference state).trans
              normalized)).map
        (fun entry => recoveredValue P
          (entry.1.read (Reusable.samplesInput P (sampleCount P)))) := by
  let sampler := Reusable.code P (sampleCount P)
    (OrderExecution.canonicalExpansion P)
  let sampled := sampler.execute (Reusable.sourceEnvironment P) Reference state
  let retainedRead := fun entry : Store (outputContext P) ×
      ((Reusable.model P).HiddenState ×
        ((History × sampler.Path) × (outputAllocation P).Path)) =>
    recoveredValue P
      (.fixedVector fun index => entry.1.read (retainedSample P index))
  let sampledRead := fun entry : Store (sampledContext P) ×
      ((Reusable.model P).HiddenState × (History × sampler.Path)) =>
    recoveredValue P (entry.1.read (Reusable.samplesInput P (sampleCount P)))
  have sampledNormalized : sampled.IsNormalized :=
    (sampler.execute_mass (Reusable.sourceEnvironment P) Reference state).trans normalized
  have retainedNormalized : (retainedState P sampled).IsNormalized :=
    binaryEndpoint_retainedState_normalized P sampled sampledNormalized
  have observed := observed_pmf_congr ((code P).execute
    (Reusable.sourceEnvironment P) Reference state)
    (retainedState P sampled)
    (((code P).execute_mass (Reusable.sourceEnvironment P) Reference state).trans normalized)
    retainedNormalized
    (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef))
    retainedRead
    (binaryEndpoint_code_observed P state)
  refine observed.trans ?_
  have readPreserved : retainedRead ∘ retainedEntry P = sampledRead := by
    funext entry
    apply congrArg (recoveredValue P)
    rw [Reusable.samplesInput]
    change CShape.Value.fixedVector (fun index =>
        (retainedEntry P entry).1.read (retainedSample P index)) =
      CShape.Value.fixedVector (fun index => entry.1.read (Reusable.sampleInput P index))
    apply congrArg CShape.Value.fixedVector
    funext index
    exact binaryEndpoint_retainedEntry_read_sample P entry index
  change ((retainedState P sampled).toPMF retainedNormalized).map retainedRead =
    (sampled.toPMF sampledNormalized).map sampledRead
  rw [binaryEndpoint_retainedState_toPMF P sampled sampledNormalized, PMF.map_comp, readPreserved]

/-- Before using independence, the endpoint distribution is exactly the raw
batch distribution mapped through its actual deterministic recovery tail. -/
public lemma binaryEndpoint_run_outputDistribution_raw (P : KnownOrderProblem G)
    {Reference : Register}
    (input : OracleInput (Reusable.model P).classicalOracles
      Reusable.pre Reference) :
    (run P).outputDistribution (Reusable.sourceEnvironment P) input =
      ((Reusable.run P (sampleCount P)
        (OrderExecution.canonicalExpansion P)).outputDistribution
          (Reusable.sourceEnvironment P) input).map
          (recoveredValue P) := by
  let entered : State Reusable.pre Reference
      ((Reusable.model P).HiddenState × Store Reusable.pre) :=
    input.state.mapClassical (fun value => (value.1, (value.2, value.1)))
  have normalized := input.state.mapClassical_normalized input.normalized
    (fun value => (value.1, (value.2, value.1)))
  have actual := code_observed_probability P entered normalized
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.executionDistribution, PMF.map_comp]
  change ((((code P).execute (Reusable.sourceEnvironment P) Reference entered).toPMF
      (((code P).execute_mass
        (Reusable.sourceEnvironment P) Reference entered).trans normalized)).map
        (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef))) =
    (((Reusable.code P (sampleCount P)
      (OrderExecution.canonicalExpansion P)).execute
        (Reusable.sourceEnvironment P) Reference entered).toPMF
        (((Reusable.code P (sampleCount P)
          (OrderExecution.canonicalExpansion P)).execute_mass
            (Reusable.sourceEnvironment P) Reference entered).trans
            normalized)).map
      (fun entry => recoveredValue P
        (entry.1.read (Reusable.samplesInput P (sampleCount P))))
  exact actual

/-- Any trace-derived independent law for the actual batch closes the complete
endpoint law without an additional sampling or recovery assumption. -/
public lemma binaryEndpoint_run_outputDistribution_of_batch (P : KnownOrderProblem G)
    {Reference : Register}
    (input : OracleInput (Reusable.model P).classicalOracles
      Reusable.pre Reference)
    (batchLaw :
      ((Reusable.run P (sampleCount P)
        (OrderExecution.canonicalExpansion P)).outputDistribution
          (Reusable.sourceEnvironment P) input).map
          (Reusable.observedVector P (sampleCount P)) =
        PMF.independentReplicateVector
          (Binary.outcomePMF P (OrderExecution.canonicalExpansion P))
          (sampleCount P)) :
    (run P).outputDistribution (Reusable.sourceEnvironment P) input = outputLaw P := by
  rw [binaryEndpoint_run_outputDistribution_raw]
  let raw := (Reusable.run P (sampleCount P)
    (OrderExecution.canonicalExpansion P)).outputDistribution (Reusable.sourceEnvironment P) input
  have recoveryFactor :
      recoveredValue P = recoveredOutcome P ∘
        Reusable.observedVector P (sampleCount P) := by
    funext samples
    change recoveredValue P samples = recoveredValue P
      (rawSamples P (sampleCount P)
        (Reusable.observedVector P (sampleCount P) samples))
    rw [binaryEndpoint_rawSamples_observed]
  rw [recoveryFactor, ← PMF.map_comp, batchLaw]
  rfl

/-- The actual one-bank execution and checked recovery have the stated complete output law. -/
public lemma binaryEndpoint_run_outputDistribution (P : KnownOrderProblem G)
    {Reference : Register}
    (input : OracleInput (Reusable.model P).classicalOracles Reusable.pre Reference) :
    (run P).outputDistribution (Reusable.sourceEnvironment P) input = outputLaw P := by
  exact binaryEndpoint_run_outputDistribution_of_batch P input
    (Reusable.reusable_run_outputDistribution P (sampleCount P)
      (OrderExecution.canonicalExpansion P) input)

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint
