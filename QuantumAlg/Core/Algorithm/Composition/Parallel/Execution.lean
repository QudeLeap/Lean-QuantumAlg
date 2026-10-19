/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.Composition.Parallel.Frame
import all QuantumAlg.Core.Execution.Composition.Laws
import all QuantumAlg.Core.Execution.Circuit

/-!
# Original child executions as marginals of actual parallel execution

Both equalities retain the complete selected final Store, selected current
service, original input history, actual child path, and original quantum
reference. The right child is compared with its original unconditional input,
using preservation of that full subsystem by the actual left execution.
-/

namespace QuantumAlg

noncomputable section

open Execution

attribute [local instance] Classical.decEq

private lemma project_parallel_left_record
    {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
    (placement : ContextEmbedding localCtx caller)
    {left right parent : ClassicalOracleModel}
    (join : ClassicalOracleModel.ServiceJoin left right parent)
    {Reference : Register} {H P Q : Type} [Fintype H] [Fintype P] [Fintype Q]
    (state : State caller Reference (parent.HiddenState × ((H × P) × Q))) :
    (placement.projectState (selectServiceLeft join (state.mapHistory
      (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2))))))).mapHistory
        (fun record => (record.1, (record.2.1, record.2.2.1))) =
      (placement.projectState (selectServiceLeft join state)).mapHistory
        (fun record => (record.1, record.2.1)) := by
  simp only [selectServiceLeft, ContextEmbedding.projectState_mapHistory,
    State.mapHistory_comp, Function.comp_def]

private lemma project_parallel_right_record
    {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
    (placement : ContextEmbedding localCtx caller)
    {left right parent : ClassicalOracleModel}
    (join : ClassicalOracleModel.ServiceJoin left right parent)
    {Reference : Register} {H P Q : Type} [Fintype H] [Fintype P] [Fintype Q]
    (state : State caller Reference (parent.HiddenState × ((H × P) × Q))) :
    (placement.projectState (selectServiceRight join (state.mapHistory
      (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2))))))).mapHistory
        (fun record => (record.1, (record.2.1, record.2.2.2))) =
      (placement.projectState (selectServiceRight join state)).mapHistory
        (fun record => (record.1, (record.2.1.1, record.2.2))) := by
  simp only [selectServiceRight, ContextEmbedding.projectState_mapHistory,
    State.mapHistory_comp, Function.comp_def]

namespace Circuit

section Classical

variable {operations : ClassicalOpModel}
  {leftService rightService parentService : ClassicalOracleModel}
  {left right : RuntimeCtx .classical} {allowAllocation : Bool}
  (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
  (separate : RuntimeCtx.StorageDisjoint left right)
  (first : Circuit (.classical operations leftService) left left false)
  (second : Circuit (.classical operations rightService) right right false)
  (environment : (ExecutionModel.classical operations parentService).Environment)
  (Reference : Register) {H : Type} [Fintype H]
  (state : State (left.disjointUnion right separate) Reference (parentService.HiddenState × H))

/-- The classical parallel left marginal is its original full child execution. -/
lemma parallelClassical_project_left :
    ((ContextEmbedding.alongUnion left right separate).projectState
      (selectServiceLeft join
        ((Circuit.parallelClassical (allowAllocation := allowAllocation)
          join separate first second).execute environment Reference state))).mapHistory
            (fun record => (record.1, (record.2.1, record.2.2.1))) =
      first.execute
      ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference
        ((ContextEmbedding.alongUnion left right separate).projectState
          (selectServiceLeft join state)) := by
  let firstCall : Circuit (.classical operations leftService)
      (left.disjointUnion right separate) (left.disjointUnion right separate) false :=
    .embed (ContextEmbedding.alongUnion left right separate) first
  let secondCall : Circuit (.classical operations rightService)
      (left.disjointUnion right separate) (left.disjointUnion right separate) false :=
    .embed (ContextEmbedding.alongUnionRight left right separate) second
  let afterLeft := serviceOutputLeft join
    (firstCall.execute
      ⟨environment.quantum, join.interpretationLeft environment.classical⟩
      Reference (serviceInputLeft join state))
  let afterRight := serviceOutputRight join
    (secondCall.execute
      ⟨environment.quantum, join.interpretationRight environment.classical⟩
      Reference (serviceInputRight join afterLeft))
  have actual :
      (Circuit.parallelClassical (allowAllocation := allowAllocation)
        join separate first second).execute environment Reference state =
        afterRight.mapHistory (fun record =>
          (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) :=
    (circuit_execute_parallelClassical join separate first second
      (environment := environment) Reference state).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  rw [actual]
  refine (project_parallel_left_record
    (ContextEmbedding.alongUnion left right separate) join afterRight).trans ?_
  exact (serviceRight_embed_preserves_left_projection
    (model := .classical operations rightService) (Reference := Reference)
    (environment := ⟨environment.quantum, join.interpretationRight environment.classical⟩)
    join separate second afterLeft).trans
      (serviceLeft_embed_projectState
        (model := .classical operations leftService)
        (ContextEmbedding.alongUnion left right separate)
        first ⟨environment.quantum, join.interpretationLeft environment.classical⟩
        Reference join state)

/-- The classical parallel right marginal uses its original input before the left child ran. -/
lemma parallelClassical_project_right :
    ((ContextEmbedding.alongUnionRight left right separate).projectState
      (selectServiceRight join
        ((Circuit.parallelClassical (allowAllocation := allowAllocation)
          join separate first second).execute environment Reference state))).mapHistory
            (fun record => (record.1, (record.2.1, record.2.2.2))) =
      second.execute
      ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
        ((ContextEmbedding.alongUnionRight left right separate).projectState
          (selectServiceRight join state)) := by
  let firstCall : Circuit (.classical operations leftService)
      (left.disjointUnion right separate) (left.disjointUnion right separate) false :=
    .embed (ContextEmbedding.alongUnion left right separate) first
  let secondCall : Circuit (.classical operations rightService)
      (left.disjointUnion right separate) (left.disjointUnion right separate) false :=
    .embed (ContextEmbedding.alongUnionRight left right separate) second
  let afterLeft := serviceOutputLeft join
    (firstCall.execute
      ⟨environment.quantum, join.interpretationLeft environment.classical⟩
      Reference (serviceInputLeft join state))
  let afterRight := serviceOutputRight join
    (secondCall.execute
      ⟨environment.quantum, join.interpretationRight environment.classical⟩
      Reference (serviceInputRight join afterLeft))
  have actual :
      (Circuit.parallelClassical (allowAllocation := allowAllocation)
        join separate first second).execute environment Reference state =
        afterRight.mapHistory (fun record =>
          (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) :=
    (circuit_execute_parallelClassical join separate first second
      (environment := environment) Reference state).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  rw [actual]
  refine (project_parallel_right_record
    (ContextEmbedding.alongUnionRight left right separate) join afterRight).trans ?_
  calc
    _ = (second.execute
      ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
        ((ContextEmbedding.alongUnionRight left right separate).projectState
          (selectServiceRight join afterLeft))).mapHistory
            (fun record => (record.1, (record.2.1.1, record.2.2))) :=
      congrArg (fun current : State right Reference
          (rightService.HiddenState × ((H × firstCall.Path) × second.Path)) =>
        current.mapHistory (fun record => (record.1, (record.2.1.1, record.2.2))))
        (serviceRight_embed_projectState
          (model := .classical operations rightService)
          (ContextEmbedding.alongUnionRight left right separate) second
          ⟨environment.quantum, join.interpretationRight environment.classical⟩
          Reference join afterLeft)
    _ = second.execute
      ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
        (((ContextEmbedding.alongUnionRight left right separate).projectState
          (selectServiceRight join afterLeft)).mapHistory
            (fun record => (record.1, record.2.1))) :=
      (second.execute_mapHistory
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
        ((ContextEmbedding.alongUnionRight left right separate).projectState
          (selectServiceRight join afterLeft)) Prod.fst).symm
    _ = _ := congrArg (second.execute
      ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference)
      (serviceLeft_embed_preserves_right_projection
        (model := .classical operations leftService) (Reference := Reference)
        (environment := ⟨environment.quantum, join.interpretationLeft environment.classical⟩)
        join separate first state)

end Classical

section Quantum

variable {gates : GateModel} {oracles : OracleModel} {operations : ClassicalOpModel}
  {leftService rightService parentService : ClassicalOracleModel}
  {left right : RuntimeCtx .quantum} {allowAllocation : Bool}
  (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
  (separate : RuntimeCtx.StorageDisjoint left right)
  (first : Circuit (.quantum gates oracles operations leftService) left left false)
  (second : Circuit (.quantum gates oracles operations rightService) right right false)
  (environment : (ExecutionModel.quantum gates oracles operations parentService).Environment)
  (Reference : Register) {H : Type} [Fintype H]
  (state : State (left.disjointUnion right separate) Reference (parentService.HiddenState × H))

/-- The quantum parallel left marginal is its original full child execution. -/
lemma parallelQuantum_project_left :
    ((ContextEmbedding.alongUnion left right separate).projectState
      (selectServiceLeft join
        ((Circuit.parallelQuantum (allowAllocation := allowAllocation)
          join separate first second).execute environment Reference state))).mapHistory
            (fun record => (record.1, (record.2.1, record.2.2.1))) =
      first.execute
      ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference
        ((ContextEmbedding.alongUnion left right separate).projectState
          (selectServiceLeft join state)) := by
  let firstCall : Circuit (.quantum gates oracles operations leftService)
      (left.disjointUnion right separate) (left.disjointUnion right separate) false :=
    .embed (ContextEmbedding.alongUnion left right separate) first
  let secondCall : Circuit (.quantum gates oracles operations rightService)
      (left.disjointUnion right separate) (left.disjointUnion right separate) false :=
    .embed (ContextEmbedding.alongUnionRight left right separate) second
  let afterLeft := serviceOutputLeft join
    (firstCall.execute
      ⟨environment.quantum, join.interpretationLeft environment.classical⟩
      Reference (serviceInputLeft join state))
  let afterRight := serviceOutputRight join
    (secondCall.execute
      ⟨environment.quantum, join.interpretationRight environment.classical⟩
      Reference (serviceInputRight join afterLeft))
  have actual :
      (Circuit.parallelQuantum (allowAllocation := allowAllocation)
        join separate first second).execute environment Reference state =
        afterRight.mapHistory (fun record =>
          (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) :=
    (circuit_execute_parallelQuantum join separate first second
      (environment := environment) Reference state).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  rw [actual]
  refine (project_parallel_left_record
    (ContextEmbedding.alongUnion left right separate) join afterRight).trans ?_
  exact (serviceRight_embed_preserves_left_projection
    (model := .quantum gates oracles operations rightService) (Reference := Reference)
    (environment := ⟨environment.quantum, join.interpretationRight environment.classical⟩)
    join separate second afterLeft).trans
      (serviceLeft_embed_projectState
        (model := .quantum gates oracles operations leftService)
        (ContextEmbedding.alongUnion left right separate)
        first ⟨environment.quantum, join.interpretationLeft environment.classical⟩
        Reference join state)

/-- The quantum parallel right marginal uses its original joint input with all correlations. -/
lemma parallelQuantum_project_right :
    ((ContextEmbedding.alongUnionRight left right separate).projectState
      (selectServiceRight join
        ((Circuit.parallelQuantum (allowAllocation := allowAllocation)
          join separate first second).execute environment Reference state))).mapHistory
            (fun record => (record.1, (record.2.1, record.2.2.2))) =
      second.execute
      ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
        ((ContextEmbedding.alongUnionRight left right separate).projectState
          (selectServiceRight join state)) := by
  let firstCall : Circuit (.quantum gates oracles operations leftService)
      (left.disjointUnion right separate) (left.disjointUnion right separate) false :=
    .embed (ContextEmbedding.alongUnion left right separate) first
  let secondCall : Circuit (.quantum gates oracles operations rightService)
      (left.disjointUnion right separate) (left.disjointUnion right separate) false :=
    .embed (ContextEmbedding.alongUnionRight left right separate) second
  let afterLeft := serviceOutputLeft join
    (firstCall.execute
      ⟨environment.quantum, join.interpretationLeft environment.classical⟩
      Reference (serviceInputLeft join state))
  let afterRight := serviceOutputRight join
    (secondCall.execute
      ⟨environment.quantum, join.interpretationRight environment.classical⟩
      Reference (serviceInputRight join afterLeft))
  have actual :
      (Circuit.parallelQuantum (allowAllocation := allowAllocation)
        join separate first second).execute environment Reference state =
        afterRight.mapHistory (fun record =>
          (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) :=
    (circuit_execute_parallelQuantum join separate first second
      (environment := environment) Reference state).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  rw [actual]
  refine (project_parallel_right_record
    (ContextEmbedding.alongUnionRight left right separate) join afterRight).trans ?_
  calc
    _ = (second.execute
      ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
        ((ContextEmbedding.alongUnionRight left right separate).projectState
          (selectServiceRight join afterLeft))).mapHistory
            (fun record => (record.1, (record.2.1.1, record.2.2))) :=
      congrArg (fun current : State right Reference
          (rightService.HiddenState × ((H × firstCall.Path) × second.Path)) =>
        current.mapHistory (fun record => (record.1, (record.2.1.1, record.2.2))))
        (serviceRight_embed_projectState
          (model := .quantum gates oracles operations rightService)
          (ContextEmbedding.alongUnionRight left right separate) second
          ⟨environment.quantum, join.interpretationRight environment.classical⟩
          Reference join afterLeft)
    _ = second.execute
      ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
        (((ContextEmbedding.alongUnionRight left right separate).projectState
          (selectServiceRight join afterLeft)).mapHistory
            (fun record => (record.1, record.2.1))) :=
      (second.execute_mapHistory
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
        ((ContextEmbedding.alongUnionRight left right separate).projectState
          (selectServiceRight join afterLeft)) Prod.fst).symm
    _ = _ := congrArg (second.execute
      ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference)
      (serviceLeft_embed_preserves_right_projection
        (model := .quantum gates oracles operations leftService) (Reference := Reference)
        (environment := ⟨environment.quantum, join.interpretationLeft environment.classical⟩)
        join separate first state)

end Quantum

end Circuit

end

end QuantumAlg
