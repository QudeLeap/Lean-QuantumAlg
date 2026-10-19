/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Recovery.Reference
import all QuantumAlg.Core.Execution.Classical.Support

/-!
# Complete recovery probabilities from the declared original-width oracle bank

The declared physical joint source read supplies the parameter of its own decoded
residue on every positive execution block. The original deterministic
recovery therefore writes the pure recovery of those same sixteen samples.
Complete observed density operators agree before taking their traces, so
arbitrary external-reference correlations remain admissible. Both the first
run and later paid bank reuse yield the original optional factor law.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch.Recovery

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] Batch.context Batch.code Batch.nextBatch into step

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

private lemma sequence_read {N : Nat} (input : Input N)
    {pre middle post : RuntimeCtx .quantum}
    (first : Circuit (model N) pre middle)
    (second : Circuit (model N) middle post)
    {Reference : Register} {History Value : Type} [Fintype History] [Fintype Value]
    (state : State pre Reference ((model N).HiddenState × History))
    (read : Store post → Value) :
    ((first.seq second).execute (sourceEnvironment input) Reference state).mapClassical (fun
      entry => read entry.1) =
      (second.execute (sourceEnvironment input) Reference (first.execute (sourceEnvironment
        input) Reference state)).mapClassical
        (fun entry => read entry.1) := by
  have executed := congrArg
    (fun output : State post Reference
        ((model N).HiddenState × (History × (first.seq second).Path)) =>
      output.mapClassical (fun entry => read entry.1))
    (Circuit.execute_seq (environment := (sourceEnvironment input)) first second state)
  refine executed.trans ?_
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]

private lemma map_law {A B C : Type} (distribution : PMF A)
    (observe : A → B) (recover : B → C) (source : PMF B) (result : PMF C)
    (first : distribution.map observe = source) (second : source.map recover = result) :
    distribution.map (recover ∘ observe) = result :=
  (PMF.map_comp observe distribution recover).symm.trans
    ((congrArg (fun probability : PMF B => probability.map recover) first).trans second)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

attribute [local irreducible] SourceRecovery.packedValue

private lemma recovered_source {origin : RuntimeCtx .quantum}
    (input : Input N)
    (sampler : Circuit (model N) origin (Batch.context base noQuantum N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State origin Reference ((model N).HiddenState × History))
    (normalized : state.IsNormalized)
    (sourceLaw : (((sampler.execute (sourceEnvironment input) Reference state).toPMF
      ((sampler.execute_mass (sourceEnvironment input) Reference state).trans normalized)).map
        (fun entry => entry.1.read (Batch.sourceRead base noQuantum N))) =
      Batch.sourceDistribution input) :
    ((((sampler.seq (into base noQuantum N input)).execute (sourceEnvironment input) Reference
      state).toPMF
      (((sampler.seq (into base noQuantum N input)).execute_mass (sourceEnvironment input)
        Reference state).trans
        normalized)).map (fun entry =>
          entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef))) =
      (sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue := by
  have beforeNormalized := (sampler.execute_mass (sourceEnvironment input) Reference
    state).trans normalized
  have observed := (sequence_read input sampler (into base noQuantum N input) state
    (fun store => store.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef))).trans
      (into_factor_read (environment := sourceEnvironment input) base noQuantum N input
        (sampler.execute (sourceEnvironment input) Reference state)
        beforeNormalized sourceLaw)
  have distribution := observed_pmf_congr
    ((sampler.seq (into base noQuantum N input)).execute (sourceEnvironment input) Reference state)
    (sampler.execute (sourceEnvironment input) Reference state)
    (((sampler.seq (into base noQuantum N input)).execute_mass (sourceEnvironment input)
      Reference state).trans normalized)
    beforeNormalized
    (fun entry => entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef))
    (fun entry => SourceRecovery.packedValue
      (entry.1.read (Batch.sourceRead base noQuantum N))) observed
  refine distribution.trans ?_
  have pushed := map_law
    ((sampler.execute (sourceEnvironment input) Reference state).toPMF beforeNormalized)
    (fun entry => entry.1.read (Batch.sourceRead base noQuantum N))
    (SourceRecovery.packedValue (N := N))
    (Batch.sourceDistribution input)
    ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
    sourceLaw (SourceRecovery.sourceDistribution_map_packedValue input)
  exact pushed

/-- The real first batch and original recovery have the original optional factor distribution. -/
lemma run_outputDistribution (input : Input N)
    {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles base Reference) :
    (run base noQuantum N input).outputDistribution (sourceEnvironment input) original =
      (sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue := by
  let entered : State base Reference ((model N).HiddenState × Store base) :=
    original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  have normalized := original.state.mapClassical_normalized original.normalized
    (fun entry => (entry.1, (entry.2, entry.1)))
  exact recovered_source base noQuantum N input (Batch.code base noQuantum N)
    entered normalized
    (Batch.source_toPMF base noQuantum N input entered normalized)

/-- Every later redraw, paid bank reuse and recovery has the same factor law on arbitrary input. -/
lemma nextRun_outputDistribution (input : Input N)
    {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles
      (Batch.context base noQuantum N) Reference) :
    (nextRun base noQuantum N input).outputDistribution (sourceEnvironment input) original =
      (sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue := by
  let entered : State (Batch.context base noQuantum N) Reference
      ((model N).HiddenState × Store (Batch.context base noQuantum N)) :=
    original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  have normalized := original.state.mapClassical_normalized original.normalized
    (fun entry => (entry.1, (entry.2, entry.1)))
  exact recovered_source base noQuantum N input (Batch.nextBatch base noQuantum N)
    entered normalized
    (Batch.next_source_toPMF base noQuantum N input entered normalized)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch.Recovery
