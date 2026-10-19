/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.Composition.Parallel.Service
import all QuantumAlg.Core.Algorithm.Composition.Parallel.Projection
import all QuantumAlg.Core.Execution.Input.Oracle.Embedding
import all QuantumAlg.Core.Execution.Input.Oracle.Service

/-!
# Original input records after physical and service projection

The local initial Store retained by each original child is the corresponding
part of the actual caller's retained initial Store. Summing the other service
and complement does not condition on either one's original value.
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

open Execution

attribute [local instance] Classical.decEq

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller)
  {left right parent : ClassicalOracleModel}
  (join : ClassicalOracleModel.ServiceJoin left right parent)
  {Reference : Register} (input : OracleInput parent caller Reference)

/-- The selected left execution retains precisely the original child's local input Store. -/
lemma projectState_left_inputRecord :
    (placement.projectState (selectServiceLeft join
      (input.state.mapClassical (fun record => (record.1, (record.2, record.1)))))).mapHistory
        (fun record => (record.1, (placement.store record.2).1)) =
      (placement.localInput (join.leftInput input)).state.mapClassical
        (fun record => (record.1, (record.2, record.1))) := by
  dsimp only [projectState, selectServiceLeft, State.mapHistory,
    localInput, framedInput, split, OracleInput.forgetReferenceFrame,
    ClassicalOracleModel.ServiceJoin.leftInput]
  simp only [← ExecutionState.forgetReferenceFrame_mapClassical,
    ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.executionState_mapClassical_comp]
  apply congrArg (fun current : ExecutionState
      (Store localCtx × (left.HiddenState × Store localCtx))
      (caller.register.prod Reference) =>
    (current.reindex
      (S := localCtx.register.prod (placement.frame.register.prod Reference))
      (placement.referenceBasis Reference)).forgetReferenceFrame)
  exact ExecutionState.executionState_mapClassical_congr input.state rfl

/-- The selected right execution retains precisely the original child's local input Store. -/
lemma projectState_right_inputRecord :
    (placement.projectState (selectServiceRight join
      (input.state.mapClassical (fun record => (record.1, (record.2, record.1)))))).mapHistory
        (fun record => (record.1, (placement.store record.2).1)) =
      (placement.localInput (join.rightInput input)).state.mapClassical
        (fun record => (record.1, (record.2, record.1))) := by
  dsimp only [projectState, selectServiceRight, State.mapHistory,
    localInput, framedInput, split, OracleInput.forgetReferenceFrame,
    ClassicalOracleModel.ServiceJoin.rightInput]
  simp only [← ExecutionState.forgetReferenceFrame_mapClassical,
    ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.executionState_mapClassical_comp]
  apply congrArg (fun current : ExecutionState
      (Store localCtx × (right.HiddenState × Store localCtx))
      (caller.register.prod Reference) =>
    (current.reindex
      (S := localCtx.register.prod (placement.frame.register.prod Reference))
      (placement.referenceBasis Reference)).forgetReferenceFrame)
  exact ExecutionState.executionState_mapClassical_congr input.state rfl

end

end QuantumAlg.ContextEmbedding
