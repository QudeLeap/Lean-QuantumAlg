/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.Composition
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Input.Oracle.Embedding
import all QuantumAlg.Core.Execution.Composition.Laws
import all QuantumAlg.Core.Execution.Composition.Coordinates
import all QuantumAlg.Core.Execution.Composition.History
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.State.Coordinates
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# The original child execution inside an embedded algorithm

The observation retains the complete local final store, current service state,
original local input store, actual path and every quantum reference coherence.
The frame's classical store is summed without conditioning. Its quantum systems
remain in the external reference of the original child run.
-/

namespace QuantumAlg.Algorithm

noncomputable section

open Execution

attribute [local instance] Classical.decEq

variable {model : ExecutionModel} {localCtx caller : RuntimeCtx model.kind}
  {shape : CShape} {allowAllocation : Bool}
  (placement : ContextEmbedding localCtx caller)
  (child : Algorithm model localCtx localCtx shape false)
  {environment : model.Environment}
  {Reference : Register} (input : OracleInput model.classicalOracles caller Reference)

/-- Projecting the actual embedded result gives the original child's complete framed run. -/
lemma embed_execute_framed :
    (placement.split
      ((embed (allowAllocation := allowAllocation) placement child).run.execute
        environment Reference input.state)).mapClassical (D := child.run.Record)
          (fun record => (record.1, (record.2.2.1,
            ((placement.store record.2.2.2.1).1, record.2.2.2.2)))) =
      child.run.execute environment (placement.frame.register.prod Reference)
        (placement.framedInput input).state := by
  let original : State caller Reference (model.HiddenState × Store caller) :=
    input.state.mapClassical
    (fun record => (record.1, (record.2, record.1)))
  let inner : State localCtx (placement.frame.register.prod Reference)
      (model.HiddenState × (Store placement.frame × Store caller)) :=
    (placement.split original).mapClassical
      (fun record => (record.1, (record.2.2.1, (record.2.1, record.2.2.2))))
  let historyMap : Store placement.frame × Store caller → Store localCtx :=
    fun record => (placement.store record.2).1
  have initial : inner.mapHistory (fun record => (record.1, historyMap record.2)) =
      (placement.framedInput input).state.mapClassical
        (fun record => (record.1, (record.2, record.1))) := by
    dsimp only [inner, original, historyMap, State.mapHistory,
      ContextEmbedding.framedInput, ContextEmbedding.split]
    simp only [ExecutionState.coordinate_reindex_mapClassical,
      ExecutionState.executionState_mapClassical_comp]
    apply congrArg (fun current : ExecutionState
        (Store localCtx × (model.HiddenState × Store localCtx))
        (caller.register.prod Reference) =>
      current.reindex
        (S := localCtx.register.prod (placement.frame.register.prod Reference))
        (placement.referenceBasis Reference))
    exact ExecutionState.executionState_mapClassical_congr input.state rfl
  change (placement.split
      ((Circuit.embed (allowAllocation := allowAllocation) placement child.run.code).execute
        environment Reference original)).mapClassical (D := child.run.Record)
          (fun record => (record.1, (record.2.2.1,
            ((placement.store record.2.2.2.1).1, record.2.2.2.2)))) =
    child.run.code.execute environment (placement.frame.register.prod Reference)
      ((placement.framedInput input).state.mapClassical
        (fun record => (record.1, (record.2, record.1))))
  rw [Circuit.circuit_execute_embed, placement.contextEmbedding_split_join,
    ExecutionState.executionState_mapClassical_comp]
  calc
    _ = (child.run.code.execute environment
        (placement.frame.register.prod Reference) inner).mapHistory
        (fun record => (record.1, (historyMap record.2.1, record.2.2))) :=
      ExecutionState.executionState_mapClassical_congr _ rfl
    _ = child.run.code.execute environment (placement.frame.register.prod Reference)
        (inner.mapHistory (fun record => (record.1, historyMap record.2))) :=
      (child.run.code.execute_mapHistory environment _ inner historyMap).symm
    _ = _ := congrArg
      (child.run.code.execute environment (placement.frame.register.prod Reference)) initial

/-- Every classical observation of the original child follows from the complete projection. -/
lemma embed_observe_framed {Result : Type} [Fintype Result] [DecidableEq Result]
    (read : child.run.Record → Result) :
    (((embed (allowAllocation := allowAllocation) placement child).run.execute
      environment Reference input.state).mapClassical (fun record =>
        read ((placement.store record.1).1,
          (record.2.1, ((placement.store record.2.2.1).1, record.2.2.2))))).reindex
        (S := localCtx.register.prod (placement.frame.register.prod Reference))
        (placement.referenceBasis Reference) =
      (child.run.execute environment (placement.frame.register.prod Reference)
        (placement.framedInput input).state).mapClassical read := by
  have projected := congrArg (fun current : ExecutionState child.run.Record
      (localCtx.register.prod (placement.frame.register.prod Reference)) =>
    current.mapClassical read)
      (embed_execute_framed (allowAllocation := allowAllocation) placement child
        (environment := environment) input)
  dsimp only [ContextEmbedding.split] at projected
  rw [ExecutionState.executionState_mapClassical_comp_instances
      (result := (inferInstance : DecidableEq Result)),
    ExecutionState.composition_reindex_mapClassical
      (secondDecision := (inferInstance : DecidableEq Result)),
    ExecutionState.executionState_mapClassical_comp_instances
      (result := (inferInstance : DecidableEq Result))] at projected
  refine Eq.trans ?_ projected
  apply congrArg (fun current : ExecutionState Result (caller.register.prod Reference) =>
    current.reindex
      (S := localCtx.register.prod (placement.frame.register.prod Reference))
      (placement.referenceBasis Reference))
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Algorithm
