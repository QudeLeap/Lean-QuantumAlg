/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Composition
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Algorithm.Problem.Embedding
import all QuantumAlg.Core.Algorithm.Composition
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Borrowed
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Problem.Embedding.Admission
import all QuantumAlg.Core.Execution.Borrowed.Embedding.Restoration
import all QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Circuit.ClassicalTag.Admission
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Execution.Input.Oracle.Embedding
import all QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Core.Execution.State.Coordinates

/-!
# Borrowed restoration for an algorithm at its physical placement

The original child contract applies to the actual framed input with its entire
classical frame encoded in the external reference. That input has precisely
the original unconditional caller and service marginals, so the same arbitrary
admission predicates hold. Pure mathematical history can be forgotten before
applying the contract and restored afterwards by interpreter naturality. The
frame store tag remains in the reference throughout that history argument.
-/

namespace QuantumAlg

noncomputable section

attribute [local instance] Classical.decEq

open Execution

namespace Algorithm

/-- The placed algorithm restores the entire borrowed CQ state on every admitted caller input. -/
public lemma algorithm_embed_borrowed
    {model : ExecutionModel} {localCtx caller : RuntimeCtx model.kind} {shape : CShape}
    {allowAllocation : Bool} (placement : ContextEmbedding localCtx caller)
    (child : Algorithm model localCtx localCtx shape false)
    (problem : Problem model localCtx localCtx shape) (correct : child.Solves problem)
    (environment : model.Environment) (witness : problem.Witness)
    {Reference : Register} (input : OracleInput model.classicalOracles caller Reference)
    (admitted : (problem.embed placement).Admits environment witness input) :
    (embed (allowAllocation := allowAllocation) placement child).run.RestoresBorrowed
      environment input := by
  let original : State caller Reference (model.HiddenState × Store caller) :=
    input.state.mapClassical (fun record => (record.1, (record.2, record.1)))
  let framed := placement.borrowedTaggedInput (model := model) original
  let encoded := State.encodeOracleTag (Tag := placement.frameStoreTag) framed
  have normalized : encoded.IsNormalized := by
    calc
      encoded.mass = framed.mass :=
        State.encodeOracleTag_mass (Tag := placement.frameStoreTag) framed
      _ = (placement.split original).mass := State.mapHistory_mass _ _
      _ = original.mass := placement.contextEmbedding_split_mass original
      _ = input.state.mass := input.state.mapClassical_mass _
      _ = 1 := input.normalized
  let tagged : OracleInput model.classicalOracles localCtx
      (placement.frameStoreTag.prod (placement.frame.register.prod Reference)) :=
    { state := encoded.mapClassical (fun record => (record.1, record.2.1))
      normalized := (encoded.mapClassical_mass _).trans normalized }
  have raw : framed.mapClassical (fun record => (record.1, record.2.1)) =
      (placement.framedInput input).state := by
    dsimp only [framed, ContextEmbedding.borrowedTaggedInput, original, State.mapHistory,
      ContextEmbedding.framedInput, ContextEmbedding.split]
    simp only [ExecutionState.coordinate_reindex_mapClassical,
      ExecutionState.executionState_mapClassical_comp]
    apply congrArg
      (fun state : ExecutionState (Store localCtx × model.HiddenState)
          (caller.register.prod Reference) =>
        state.reindex (S := localCtx.register.prod (placement.frame.register.prod Reference))
          (placement.referenceBasis Reference))
    exact ExecutionState.executionState_mapClassical_congr input.state rfl
  have localSame : tagged.localState = (placement.framedInput input).localState := by
    change (encoded.mapClassical (fun record => (record.1, record.2.1))).marginalLeft =
      (placement.framedInput input).state.marginalLeft
    rw [ExecutionState.executionState_marginalLeft_mapClassical]
    dsimp only [encoded]
    rw [State.encodeOracleTag_marginalLeft, ExecutionState.executionState_mapClassical_comp]
    calc
      _ = (framed.mapClassical (fun record => (record.1, record.2.1))).marginalLeft := by
        rw [ExecutionState.executionState_marginalLeft_mapClassical]
        rfl
      _ = _ := congrArg ExecutionState.marginalLeft raw
  have callerSame : tagged.caller.localState =
      (placement.framedInput input).caller.localState := by
    change (tagged.state.mapClassical Prod.fst).marginalLeft =
      ((placement.framedInput input).state.mapClassical Prod.fst).marginalLeft
    calc
      _ = tagged.state.marginalLeft.mapClassical Prod.fst :=
        ExecutionState.executionState_marginalLeft_mapClassical tagged.state Prod.fst
      _ = (placement.framedInput input).state.marginalLeft.mapClassical Prod.fst :=
        congrArg (fun state : ExecutionState (Store localCtx × model.HiddenState)
          localCtx.register => state.mapClassical Prod.fst) localSame
      _ = _ := (ExecutionState.executionState_marginalLeft_mapClassical
        (placement.framedInput input).state Prod.fst).symm
  have childAdmitted :=
    (Problem.problem_embed_admits_framed_iff placement problem
      environment witness input).mp admitted
  have taggedAdmitted : problem.Admits environment witness tagged := by
    constructor
    · rw [callerSame]
      exact childAdmitted.1
    · rw [localSame]
      exact childAdmitted.2
  have restored := correct.borrowed environment witness _ tagged taggedAdmitted.1 taggedAdmitted.2
  have historyRestored :=
    algorithmRun_restoresBorrowed_with_history child.run environment tagged encoded rfl restored
  have placed := Circuit.borrowedRestored_embed_of_encoded (allowAllocation := allowAllocation)
    placement child.run.code environment Reference original historyRestored
  change observeBorrowed Reference
      ((Circuit.embed (allowAllocation := allowAllocation) placement child.run.code).execute
        environment Reference original) = observeBorrowed Reference original at placed
  change observeBorrowed Reference
      ((Circuit.embed (allowAllocation := allowAllocation) placement child.run.code).execute
        environment Reference original) = observeBorrowed Reference input.state
  have forgotten := observeBorrowed_mapClassical input.state
    (fun record => (record.1, (record.2, record.1))) (fun _ => rfl)
  apply placed.trans
  refine (congrArg (observeBorrowed Reference) ?_).trans forgotten
  exact ExecutionState.executionState_mapClassical_congr input.state rfl

end Algorithm

end

end QuantumAlg
