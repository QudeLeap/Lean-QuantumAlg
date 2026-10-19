/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.Composition
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Composition.Parallel.Execution
import all QuantumAlg.Core.Algorithm.Composition.Parallel.InputRecord

/-!
# Original complete child runs inside parallel algorithms

Each marginal is the unchanged child AlgorithmRun on its own original
unconditional localInput. Initial and final local Stores, current service,
actual child path and the original external reference are retained together.
-/

namespace QuantumAlg.Algorithm

noncomputable section

open Execution

attribute [local instance] Classical.decEq

section Classical

variable {operations : ClassicalOpModel}
  {leftService rightService parentService : ClassicalOracleModel}
  {left right : RuntimeCtx .classical} {leftShape rightShape : CShape}
  {allowAllocation : Bool}
  (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
  (separate : RuntimeCtx.StorageDisjoint left right)
  (first : Algorithm (.classical operations leftService) left left leftShape false)
  (second : Algorithm (.classical operations rightService) right right rightShape false)
  (environment : (ExecutionModel.classical operations parentService).Environment)
  {Reference : Register}
  (input : OracleInput parentService (left.disjointUnion right separate) Reference)

/-- The classical parallel left projection is its original complete child run. -/
lemma parallelClassical_execute_left :
    ((ContextEmbedding.alongUnion left right separate).projectState
      (selectServiceLeft join
        ((parallelClassical (allowAllocation := allowAllocation)
          join separate first second).run.execute environment Reference input.state))).mapHistory
            (fun record => (record.1,
              (((ContextEmbedding.alongUnion left right separate).store record.2.1).1,
                record.2.2.1))) =
      first.run.execute
      ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference
        ((ContextEmbedding.alongUnion left right separate).localInput
          (join.leftInput input)).state := by
  let source : State (left.disjointUnion right separate) Reference
      (parentService.HiddenState × Store (left.disjointUnion right separate)) :=
    input.state.mapClassical (fun record => (record.1, (record.2, record.1)))
  have original := Circuit.parallelClassical_project_left
    (allowAllocation := allowAllocation) join separate first.run.code second.run.code
      environment Reference source
  have projected := congrArg
    (fun current : State left Reference
        (leftService.HiddenState ×
          (Store (left.disjointUnion right separate) × first.run.code.Path)) =>
      current.mapHistory (fun record => (record.1,
        (((ContextEmbedding.alongUnion left right separate).store record.2.1).1,
          record.2.2)))) original
  have mapped := projected.trans
    (first.run.code.execute_mapHistory
      ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference
      ((ContextEmbedding.alongUnion left right separate).projectState
        (selectServiceLeft join source))
      (fun store : Store (left.disjointUnion right separate) =>
        ((ContextEmbedding.alongUnion left right separate).store store).1)).symm
  have initialized := ContextEmbedding.projectState_left_inputRecord
    (ContextEmbedding.alongUnion left right separate) join input
  have completed := mapped.trans (congrArg (first.run.code.execute
      ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference) initialized)
  simp only [source, parallelClassical, AlgorithmRun.execute, State.mapHistory_comp,
    Function.comp_def] at completed ⊢
  refine Eq.trans ?_ (completed.trans ?_)
  · apply congrArg (fun initial : State (left.disjointUnion right separate) Reference
        (parentService.HiddenState × Store (left.disjointUnion right separate)) =>
      ((ContextEmbedding.alongUnion left right separate).projectState
        (selectServiceLeft join
          ((Circuit.parallelClassical (allowAllocation := allowAllocation)
            join separate first.run.code second.run.code).execute
              environment Reference initial))).mapHistory
              (fun record => (record.1,
                (((ContextEmbedding.alongUnion left right separate).store record.2.1).1,
                  record.2.2.1))))
    exact ExecutionState.executionState_mapClassical_congr input.state rfl
  · apply congrArg (first.run.code.execute
      ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference)
    exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The classical parallel right projection is its original complete child run. -/
lemma parallelClassical_execute_right :
    ((ContextEmbedding.alongUnionRight left right separate).projectState
      (selectServiceRight join
        ((parallelClassical (allowAllocation := allowAllocation)
          join separate first second).run.execute environment Reference input.state))).mapHistory
            (fun record => (record.1,
              (((ContextEmbedding.alongUnionRight left right separate).store record.2.1).1,
                record.2.2.2))) =
      second.run.execute
      ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
        ((ContextEmbedding.alongUnionRight left right separate).localInput
          (join.rightInput input)).state := by
  let source : State (left.disjointUnion right separate) Reference
      (parentService.HiddenState × Store (left.disjointUnion right separate)) :=
    input.state.mapClassical (fun record => (record.1, (record.2, record.1)))
  have original := Circuit.parallelClassical_project_right
    (allowAllocation := allowAllocation) join separate first.run.code second.run.code
      environment Reference source
  have projected := congrArg
    (fun current : State right Reference
        (rightService.HiddenState ×
          (Store (left.disjointUnion right separate) × second.run.code.Path)) =>
      current.mapHistory (fun record => (record.1,
        (((ContextEmbedding.alongUnionRight left right separate).store record.2.1).1,
          record.2.2)))) original
  have mapped := projected.trans
    (second.run.code.execute_mapHistory
      ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
      ((ContextEmbedding.alongUnionRight left right separate).projectState
        (selectServiceRight join source))
      (fun store : Store (left.disjointUnion right separate) =>
        ((ContextEmbedding.alongUnionRight left right separate).store store).1)).symm
  have initialized := ContextEmbedding.projectState_right_inputRecord
    (ContextEmbedding.alongUnionRight left right separate) join input
  have completed := mapped.trans (congrArg (second.run.code.execute
      ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference) initialized)
  simp only [source, parallelClassical, AlgorithmRun.execute, State.mapHistory_comp,
    Function.comp_def] at completed ⊢
  refine Eq.trans ?_ (completed.trans ?_)
  · apply congrArg (fun initial : State (left.disjointUnion right separate) Reference
        (parentService.HiddenState × Store (left.disjointUnion right separate)) =>
      ((ContextEmbedding.alongUnionRight left right separate).projectState
        (selectServiceRight join
          ((Circuit.parallelClassical (allowAllocation := allowAllocation)
            join separate first.run.code second.run.code).execute
              environment Reference initial))).mapHistory
              (fun record => (record.1,
                (((ContextEmbedding.alongUnionRight left right separate).store record.2.1).1,
                  record.2.2.2))))
    exact ExecutionState.executionState_mapClassical_congr input.state rfl
  · apply congrArg (second.run.code.execute
      ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference)
    exact ExecutionState.executionState_mapClassical_congr _ rfl

end Classical

section Quantum

variable {gates : GateModel} {oracles : OracleModel} {operations : ClassicalOpModel}
  {leftService rightService parentService : ClassicalOracleModel}
  {left right : RuntimeCtx .quantum} {leftShape rightShape : CShape}
  {allowAllocation : Bool}
  (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
  (separate : RuntimeCtx.StorageDisjoint left right)
  (first : Algorithm (.quantum gates oracles operations leftService) left left leftShape false)
  (second : Algorithm (.quantum gates oracles operations rightService) right right rightShape false)
  (environment : (ExecutionModel.quantum gates oracles operations parentService).Environment)
  {Reference : Register}
  (input : OracleInput parentService (left.disjointUnion right separate) Reference)

/-- The quantum parallel left projection is its original complete child run. -/
lemma parallelQuantum_execute_left :
    ((ContextEmbedding.alongUnion left right separate).projectState
      (selectServiceLeft join
        ((parallelQuantum (allowAllocation := allowAllocation)
          join separate first second).run.execute environment Reference input.state))).mapHistory
            (fun record => (record.1,
              (((ContextEmbedding.alongUnion left right separate).store record.2.1).1,
                record.2.2.1))) =
      first.run.execute
      ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference
        ((ContextEmbedding.alongUnion left right separate).localInput
          (join.leftInput input)).state := by
  let source : State (left.disjointUnion right separate) Reference
      (parentService.HiddenState × Store (left.disjointUnion right separate)) :=
    input.state.mapClassical (fun record => (record.1, (record.2, record.1)))
  have original := Circuit.parallelQuantum_project_left
    (allowAllocation := allowAllocation) join separate first.run.code second.run.code
      environment Reference source
  have projected := congrArg
    (fun current : State left Reference
        (leftService.HiddenState ×
          (Store (left.disjointUnion right separate) × first.run.code.Path)) =>
      current.mapHistory (fun record => (record.1,
        (((ContextEmbedding.alongUnion left right separate).store record.2.1).1,
          record.2.2)))) original
  have mapped := projected.trans
    (first.run.code.execute_mapHistory
      ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference
      ((ContextEmbedding.alongUnion left right separate).projectState
        (selectServiceLeft join source))
      (fun store : Store (left.disjointUnion right separate) =>
        ((ContextEmbedding.alongUnion left right separate).store store).1)).symm
  have initialized := ContextEmbedding.projectState_left_inputRecord
    (ContextEmbedding.alongUnion left right separate) join input
  have completed := mapped.trans (congrArg (first.run.code.execute
      ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference) initialized)
  simp only [source, parallelQuantum, AlgorithmRun.execute, State.mapHistory_comp,
    Function.comp_def] at completed ⊢
  refine Eq.trans ?_ (completed.trans ?_)
  · apply congrArg (fun initial : State (left.disjointUnion right separate) Reference
        (parentService.HiddenState × Store (left.disjointUnion right separate)) =>
      ((ContextEmbedding.alongUnion left right separate).projectState
        (selectServiceLeft join
          ((Circuit.parallelQuantum (allowAllocation := allowAllocation)
            join separate first.run.code second.run.code).execute
              environment Reference initial))).mapHistory
              (fun record => (record.1,
                (((ContextEmbedding.alongUnion left right separate).store record.2.1).1,
                  record.2.2.1))))
    exact ExecutionState.executionState_mapClassical_congr input.state rfl
  · apply congrArg (first.run.code.execute
      ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference)
    exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The quantum parallel right projection is its original complete child run. -/
lemma parallelQuantum_execute_right :
    ((ContextEmbedding.alongUnionRight left right separate).projectState
      (selectServiceRight join
        ((parallelQuantum (allowAllocation := allowAllocation)
          join separate first second).run.execute environment Reference input.state))).mapHistory
            (fun record => (record.1,
              (((ContextEmbedding.alongUnionRight left right separate).store record.2.1).1,
                record.2.2.2))) =
      second.run.execute
      ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
        ((ContextEmbedding.alongUnionRight left right separate).localInput
          (join.rightInput input)).state := by
  let source : State (left.disjointUnion right separate) Reference
      (parentService.HiddenState × Store (left.disjointUnion right separate)) :=
    input.state.mapClassical (fun record => (record.1, (record.2, record.1)))
  have original := Circuit.parallelQuantum_project_right
    (allowAllocation := allowAllocation) join separate first.run.code second.run.code
      environment Reference source
  have projected := congrArg
    (fun current : State right Reference
        (rightService.HiddenState ×
          (Store (left.disjointUnion right separate) × second.run.code.Path)) =>
      current.mapHistory (fun record => (record.1,
        (((ContextEmbedding.alongUnionRight left right separate).store record.2.1).1,
          record.2.2)))) original
  have mapped := projected.trans
    (second.run.code.execute_mapHistory
      ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
      ((ContextEmbedding.alongUnionRight left right separate).projectState
        (selectServiceRight join source))
      (fun store : Store (left.disjointUnion right separate) =>
        ((ContextEmbedding.alongUnionRight left right separate).store store).1)).symm
  have initialized := ContextEmbedding.projectState_right_inputRecord
    (ContextEmbedding.alongUnionRight left right separate) join input
  have completed := mapped.trans (congrArg (second.run.code.execute
      ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference) initialized)
  simp only [source, parallelQuantum, AlgorithmRun.execute, State.mapHistory_comp,
    Function.comp_def] at completed ⊢
  refine Eq.trans ?_ (completed.trans ?_)
  · apply congrArg (fun initial : State (left.disjointUnion right separate) Reference
        (parentService.HiddenState × Store (left.disjointUnion right separate)) =>
      ((ContextEmbedding.alongUnionRight left right separate).projectState
        (selectServiceRight join
          ((Circuit.parallelQuantum (allowAllocation := allowAllocation)
            join separate first.run.code second.run.code).execute
              environment Reference initial))).mapHistory
              (fun record => (record.1,
                (((ContextEmbedding.alongUnionRight left right separate).store record.2.1).1,
                  record.2.2.2))))
    exact ExecutionState.executionState_mapClassical_congr input.state rfl
  · apply congrArg (second.run.code.execute
      ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference)
    exact ExecutionState.executionState_mapClassical_congr _ rfl

end Quantum

end

end QuantumAlg.Algorithm

