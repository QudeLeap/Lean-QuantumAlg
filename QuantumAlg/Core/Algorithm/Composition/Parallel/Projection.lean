/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Composition.Laws
import all QuantumAlg.Core.Execution.Composition.History
import all QuantumAlg.Core.Execution.Circuit.Marginal
import all QuantumAlg.Core.Execution.Circuit.Reference.Frame
import all QuantumAlg.Core.Execution.Reference.Spectator
import all QuantumAlg.Core.Execution.State.Marginal.Reference
import all QuantumAlg.Core.Execution.State.Coordinates
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Complete local and frame observations with arbitrary histories

The physical projection retains every classical history label and the original
external reference. Complement storage is observed away only for the local
projection; the separate frame projection retains that entire complement.
-/

namespace QuantumAlg

noncomputable section

open Execution

attribute [local instance] Classical.decEq

namespace ExecutionState

/-- A later classical readout commutes with the complete reference observation. -/
lemma referenceObservation_map_result
    {C D E : Type} [Fintype C] [Fintype D] [Fintype E]
    {R Reference : Register} [DecidableEq E] (state : ExecutionState C (R.prod Reference))
    (read : C → D) (update : D → E) :
    (state.referenceObservation read).mapClassical update =
      state.referenceObservation (update ∘ read) := by
  unfold referenceObservation
  rw [← executionState_marginalLeft_mapClassical,
    coordinate_reindex_mapClassical,
    executionState_mapClassical_comp_instances (result := Classical.decEq E)]

end ExecutionState

namespace ContextEmbedding

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller) {Reference : Register}
  {H K : Type} [Fintype H] [Fintype K]

/-- Observe the actual local store, quantum systems, complete history and original reference. -/
def projectState (state : State caller Reference H) : State localCtx Reference H :=
  ((placement.split state).mapClassical
    (fun record => (record.1, record.2.2))).forgetReferenceFrame

/-- Observe the entire inaccessible frame jointly with history and the original reference. -/
def frameState (state : State caller Reference H) :
    State placement.frame Reference H :=
  (placement.split state).referenceObservation (fun record => (record.2.1, record.2.2))

/-- Physical local observation commutes with every mathematical history map. -/
lemma projectState_mapHistory (state : State caller Reference H) (update : H → K) :
    placement.projectState (state.mapHistory update) =
      (placement.projectState state).mapHistory update := by
  unfold projectState
  rw [placement.split_mapHistory]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp]
  rw [← ExecutionState.forgetReferenceFrame_mapClassical]
  apply congrArg ExecutionState.forgetReferenceFrame
  rw [ExecutionState.executionState_mapClassical_comp]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Physical frame observation retains every remapped history label jointly. -/
lemma frameState_mapHistory (state : State caller Reference H) (update : H → K) :
    placement.frameState (state.mapHistory update) =
      (placement.frameState state).mapHistory update := by
  unfold frameState
  rw [placement.split_mapHistory]
  simp only [State.mapHistory, ExecutionState.referenceObservation_mapClassical,
    ExecutionState.referenceObservation_map_result, Function.comp_def]

end ContextEmbedding

namespace Circuit

/-- The actual embedded child has the same complete local execution on its projected input. -/
lemma execute_embed_projectState
    {model : ExecutionModel} {localCtx caller : RuntimeCtx model.kind}
    {allowAllocation : Bool} (placement : ContextEmbedding localCtx caller)
    (code : Circuit model localCtx localCtx false) (environment : model.Environment)
    (Reference : Register)
    {H : Type} [Fintype H] (state : State caller Reference (model.HiddenState × H)) :
    placement.projectState
      ((Circuit.embed (allowAllocation := allowAllocation) placement code).execute
        environment Reference state) =
      code.execute environment Reference (placement.projectState state) := by
  let inner : State localCtx (placement.frame.register.prod Reference)
      (model.HiddenState × (Store placement.frame × H)) :=
    (placement.split state).mapClassical (fun record =>
      (record.1, (record.2.2.1, (record.2.1, record.2.2.2))))
  have initial : inner.mapHistory (fun record => (record.1, record.2.2)) =
      (placement.split state).mapClassical (fun record => (record.1, record.2.2)) := by
    simp only [inner, State.mapHistory, ExecutionState.executionState_mapClassical_comp]
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  unfold ContextEmbedding.projectState
  rw [circuit_execute_embed, placement.contextEmbedding_split_join,
    ExecutionState.executionState_mapClassical_comp_instances
      (result := Classical.decEq _)]
  calc
    _ = ((code.execute environment (placement.frame.register.prod Reference) inner).mapHistory
        (fun record => (record.1, (record.2.1.2, record.2.2)))).forgetReferenceFrame := by
      apply congrArg ExecutionState.forgetReferenceFrame
      exact ExecutionState.executionState_mapClassical_congr _ rfl
    _ = (code.execute environment (placement.frame.register.prod Reference)
        (inner.mapHistory (fun record => (record.1, record.2.2)))).forgetReferenceFrame :=
      congrArg ExecutionState.forgetReferenceFrame
        (code.execute_mapHistory environment _ inner Prod.snd).symm
    _ = _ := by
      rw [initial, ← code.execute_forgetReferenceFrame environment]
      apply congrArg (code.execute environment Reference)
      apply congrArg ExecutionState.forgetReferenceFrame
      exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Embedded execution preserves the complete frame jointly with every original history. -/
lemma execute_embed_frameState
    {model : ExecutionModel} {localCtx caller : RuntimeCtx model.kind}
    {allowAllocation : Bool} (placement : ContextEmbedding localCtx caller)
    (code : Circuit model localCtx localCtx false) (environment : model.Environment)
    (Reference : Register)
    {H : Type} [Fintype H] (state : State caller Reference (model.HiddenState × H)) :
    (placement.frameState
      ((Circuit.embed (allowAllocation := allowAllocation) placement code).execute
        environment Reference state)).mapHistory (fun record => record.2.1) =
      (placement.frameState state).mapHistory Prod.snd := by
  simp only [ContextEmbedding.frameState, State.mapHistory,
    ExecutionState.referenceObservation_map_result, Function.comp_def]
  exact execute_embed_frameObservation placement code environment Reference state

end Circuit

end

end QuantumAlg
