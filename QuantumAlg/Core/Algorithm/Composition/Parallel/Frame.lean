/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.Composition.Parallel.Service
import all QuantumAlg.Core.Algorithm.Composition.Parallel.UnionObservation

/-!
# Each actual service-side call preserves the opposite complete subsystem

The preserved observation contains the other physical Store and quantum
systems, the other persistent service, every old history label, and the
original external reference. The child's new path is summed, never selected.
-/

namespace QuantumAlg.Execution

noncomputable section

attribute [local instance] Classical.decEq

variable {model : ExecutionModel} {other parent : ClassicalOracleModel}
  {localCtx caller : RuntimeCtx model.kind}
  (placement : ContextEmbedding localCtx caller)
  (code : Circuit model localCtx localCtx false) (environment : model.Environment)
  (Reference : Register)
  {H : Type} [Fintype H]

/-- A real left call preserves the complete frame together with the inactive right service. -/
lemma serviceLeft_embed_frame_preserved
    (join : ClassicalOracleModel.ServiceJoin model.classicalOracles other parent)
    (state : State caller Reference (parent.HiddenState × H)) :
    (placement.frameState (serviceOutputLeft join
      ((Circuit.embed (allowAllocation := false) placement code).execute environment Reference
        (serviceInputLeft join state)))).mapHistory
          (fun record => ((join.hidden record.1).2, record.2.1)) =
      (placement.frameState state).mapHistory
        (fun record => ((join.hidden record.1).2, record.2)) := by
  calc
    _ = (placement.frameState
        ((Circuit.embed (allowAllocation := false) placement code).execute environment Reference
          (serviceInputLeft join state))).mapHistory (fun record => record.2.1) := by
      rw [serviceOutputLeft_eq_mapHistory, placement.frameState_mapHistory,
        State.mapHistory_comp]
      unfold State.mapHistory
      apply ExecutionState.executionState_mapClassical_congr
      funext record
      change (record.1, ((join.hidden (join.hidden.symm
        (record.2.1, record.2.2.1.1))).2, record.2.2.1.2)) = _
      rw [join.hidden.apply_symm_apply]
    _ = (placement.frameState (serviceInputLeft join state)).mapHistory Prod.snd :=
      Circuit.execute_embed_frameState placement code environment
        Reference (serviceInputLeft join state)
    _ = _ := by
      rw [serviceInputLeft_eq_mapHistory, placement.frameState_mapHistory,
        State.mapHistory_comp]
      unfold State.mapHistory
      exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- A real right call preserves the complete frame together with the inactive left service. -/
lemma serviceRight_embed_frame_preserved
    (join : ClassicalOracleModel.ServiceJoin other model.classicalOracles parent)
    (state : State caller Reference (parent.HiddenState × H)) :
    (placement.frameState (serviceOutputRight join
      ((Circuit.embed (allowAllocation := false) placement code).execute environment Reference
        (serviceInputRight join state)))).mapHistory
          (fun record => ((join.hidden record.1).1, record.2.1)) =
      (placement.frameState state).mapHistory
        (fun record => ((join.hidden record.1).1, record.2)) := by
  calc
    _ = (placement.frameState
        ((Circuit.embed (allowAllocation := false) placement code).execute environment Reference
          (serviceInputRight join state))).mapHistory (fun record => record.2.1) := by
      rw [serviceOutputRight_eq_mapHistory, placement.frameState_mapHistory,
        State.mapHistory_comp]
      unfold State.mapHistory
      apply ExecutionState.executionState_mapClassical_congr
      funext record
      change (record.1, ((join.hidden (join.hidden.symm
        (record.2.2.1.1, record.2.1))).1, record.2.2.1.2)) = _
      rw [join.hidden.apply_symm_apply]
    _ = (placement.frameState (serviceInputRight join state)).mapHistory Prod.snd :=
      Circuit.execute_embed_frameState placement code environment
        Reference (serviceInputRight join state)
    _ = _ := by
      rw [serviceInputRight_eq_mapHistory, placement.frameState_mapHistory,
        State.mapHistory_comp]
      unfold State.mapHistory
      exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The left local marginal is the original left child on the projected complete input. -/
lemma serviceLeft_embed_projectState
    (join : ClassicalOracleModel.ServiceJoin model.classicalOracles other parent)
    (state : State caller Reference (parent.HiddenState × H)) :
    placement.projectState (selectServiceLeft join (serviceOutputLeft join
      ((Circuit.embed (allowAllocation := false) placement code).execute environment Reference
        (serviceInputLeft join state)))) =
      code.execute environment Reference
        (placement.projectState (selectServiceLeft join state)) := by
  rw [serviceLeft_execute_select_active, Circuit.execute_embed_projectState]

/-- The right local marginal is the original right child on the projected complete input. -/
lemma serviceRight_embed_projectState
    (join : ClassicalOracleModel.ServiceJoin other model.classicalOracles parent)
    (state : State caller Reference (parent.HiddenState × H)) :
    placement.projectState (selectServiceRight join (serviceOutputRight join
      ((Circuit.embed (allowAllocation := false) placement code).execute environment Reference
        (serviceInputRight join state)))) =
      code.execute environment Reference
        (placement.projectState (selectServiceRight join state)) := by
  rw [serviceRight_execute_select_active, Circuit.execute_embed_projectState]

/-- The left call cannot change the original right joint input after its own path is forgotten. -/
lemma serviceLeft_embed_preserves_right_projection
    {left right : RuntimeCtx model.kind}
    (join : ClassicalOracleModel.ServiceJoin model.classicalOracles other parent)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (body : Circuit model left left false)
    (state : State (left.disjointUnion right separate) Reference (parent.HiddenState × H)) :
    ((ContextEmbedding.alongUnionRight left right separate).projectState
      (selectServiceRight join (serviceOutputLeft join
        ((Circuit.embed (allowAllocation := false)
          (ContextEmbedding.alongUnion left right separate) body).execute environment Reference
            (serviceInputLeft join state))))).mapHistory
              (fun record => (record.1, record.2.1)) =
      (ContextEmbedding.alongUnionRight left right separate).projectState
        (selectServiceRight join state) := by
  unfold selectServiceRight
  rw [ContextEmbedding.projectState_mapHistory, ContextEmbedding.projectState_mapHistory,
    State.mapHistory_comp,
    ContextEmbedding.projectState_union_right_eq_frame_left,
    ContextEmbedding.projectState_union_right_eq_frame_left]
  exact serviceLeft_embed_frame_preserved
    (ContextEmbedding.alongUnion left right separate) body environment Reference join state

/-- The right call preserves the complete left result jointly with all earlier path labels. -/
lemma serviceRight_embed_preserves_left_projection
    {left right : RuntimeCtx model.kind}
    (join : ClassicalOracleModel.ServiceJoin other model.classicalOracles parent)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (body : Circuit model right right false)
    (state : State (left.disjointUnion right separate) Reference (parent.HiddenState × H)) :
    ((ContextEmbedding.alongUnion left right separate).projectState
      (selectServiceLeft join (serviceOutputRight join
        ((Circuit.embed (allowAllocation := false)
          (ContextEmbedding.alongUnionRight left right separate) body).execute environment Reference
            (serviceInputRight join state))))).mapHistory
              (fun record => (record.1, record.2.1)) =
      (ContextEmbedding.alongUnion left right separate).projectState
        (selectServiceLeft join state) := by
  unfold selectServiceLeft
  rw [ContextEmbedding.projectState_mapHistory, ContextEmbedding.projectState_mapHistory,
    State.mapHistory_comp,
    ContextEmbedding.projectState_union_left_eq_frame_right,
    ContextEmbedding.projectState_union_left_eq_frame_right]
  exact serviceRight_embed_frame_preserved
    (ContextEmbedding.alongUnionRight left right separate) body environment Reference join state

end

end QuantumAlg.Execution
