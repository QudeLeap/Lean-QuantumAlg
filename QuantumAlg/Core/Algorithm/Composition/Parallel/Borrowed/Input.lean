/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.Composition.Parallel.Frame
import all QuantumAlg.Core.Algorithm.Composition.Parallel.Projection
import all QuantumAlg.Core.Algorithm.Composition.Parallel.Service
import all QuantumAlg.Core.Execution.Composition.Parallel
import all QuantumAlg.Core.Execution.Input.Oracle.Embedding
import all QuantumAlg.Core.Execution.Input.Oracle.Service
import all QuantumAlg.Core.Execution.State.History
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Unconditional inputs for the two borrowed restoration guarantees

Summing mathematical history retains the exact active service and physical
caller input. After the actual left call, the right child's unconditional
joint input is unchanged. The full reference state is retained in this
equality; neither an execution path nor a classical frame value is selected.
-/

namespace QuantumAlg.Execution

noncomputable section

attribute [local instance] Classical.decEq

variable {left right parent : ClassicalOracleModel}
  (join : ClassicalOracleModel.ServiceJoin left right parent)
  {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}

/-- Removing the inactive service and old history gives the original left input. -/
lemma serviceInputLeft_inputRecord_raw
    (input : OracleInput parent ctx Reference) :
    State.mapHistory (serviceInputLeft join
      (input.state.mapClassical (fun record => (record.1, (record.2, record.1))))) Prod.fst =
      (join.leftInput input).state := by
  rw [serviceInputLeft_eq_mapHistory]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    ClassicalOracleModel.ServiceJoin.leftInput]
  exact ExecutionState.executionState_mapClassical_congr input.state rfl

/-- Removing the inactive service and old history gives the original right input. -/
lemma serviceInputRight_inputRecord_raw
    (input : OracleInput parent ctx Reference) :
    State.mapHistory (serviceInputRight join
      (input.state.mapClassical (fun record => (record.1, (record.2, record.1))))) Prod.fst =
      (join.rightInput input).state := by
  rw [serviceInputRight_eq_mapHistory]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    ClassicalOracleModel.ServiceJoin.rightInput]
  exact ExecutionState.executionState_mapClassical_congr input.state rfl

/-- Both right-service coordinate presentations have the same raw active input. -/
lemma serviceInputRight_raw_eq_selected
    {H : Type} [Fintype H] (state : State ctx Reference (parent.HiddenState × H)) :
    (serviceInputRight join state).mapHistory Prod.fst =
      (selectServiceRight join state).mapHistory Prod.fst := by
  rw [serviceInputRight_eq_mapHistory, selectServiceRight,
    State.mapHistory_comp, State.mapHistory_comp]
  rfl

/-- The actual right call sees the same unconditional local input as before the left call. -/
lemma serviceLeft_embed_right_rawInput
    {model : ExecutionModel} {other parent : ClassicalOracleModel}
    {leftCtx rightCtx : RuntimeCtx model.kind}
    (join : ClassicalOracleModel.ServiceJoin model.classicalOracles other parent)
    (separate : RuntimeCtx.StorageDisjoint leftCtx rightCtx)
    (body : Circuit model leftCtx leftCtx false)
    (environment : model.Environment)
    {Reference : Register}
    (input : OracleInput parent (leftCtx.disjointUnion rightCtx separate) Reference) :
    (ContextEmbedding.alongUnionRight leftCtx rightCtx separate).projectState
      ((serviceInputRight join (serviceOutputLeft join
        ((Circuit.embed (allowAllocation := false)
          (ContextEmbedding.alongUnion leftCtx rightCtx separate) body).execute
            environment Reference
            (serviceInputLeft join (input.state.mapClassical
              (fun record => (record.1, (record.2, record.1)))))))).mapHistory Prod.fst) =
      ((ContextEmbedding.alongUnionRight leftCtx rightCtx separate).localInput
        (join.rightInput input)).state := by
  let original : State (leftCtx.disjointUnion rightCtx separate) Reference
      (parent.HiddenState × Store (leftCtx.disjointUnion rightCtx separate)) :=
    input.state.mapClassical (fun record => (record.1, (record.2, record.1)))
  let afterLeft := serviceOutputLeft join
    ((Circuit.embed (allowAllocation := false)
      (ContextEmbedding.alongUnion leftCtx rightCtx separate) body).execute
            environment Reference
        (serviceInputLeft join original))
  let placement := ContextEmbedding.alongUnionRight leftCtx rightCtx separate
  have preserved := serviceLeft_embed_preserves_right_projection
    (environment := environment) (Reference := Reference) join separate body original
  have erased := congrArg
    (fun state : State rightCtx Reference
        (other.HiddenState × Store (leftCtx.disjointUnion rightCtx separate)) =>
      state.mapHistory Prod.fst) preserved
  change placement.projectState ((serviceInputRight join afterLeft).mapHistory Prod.fst) = _
  calc
    _ = (placement.projectState (selectServiceRight join afterLeft)).mapHistory Prod.fst := by
      rw [serviceInputRight_raw_eq_selected, ContextEmbedding.projectState_mapHistory]
    _ = (placement.projectState (selectServiceRight join original)).mapHistory Prod.fst := by
      simpa only [State.mapHistory_comp, Function.comp_def] using erased
    _ = placement.projectState (join.rightInput input).state := by
      rw [← ContextEmbedding.projectState_mapHistory]
      apply congrArg placement.projectState
      exact (serviceInputRight_raw_eq_selected join original).symm.trans
        (serviceInputRight_inputRecord_raw join input)
    _ = _ := rfl

end

end QuantumAlg.Execution
