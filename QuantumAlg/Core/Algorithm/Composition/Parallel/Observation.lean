/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.Composition.Parallel.Run
import all QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.State.Marginal.Reference
import all QuantumAlg.Core.Execution.State.Coordinates
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Arbitrary observations of the original parallel child runs

Every observation is a pushforward of the exact complete child projection.
Only the other service, other final store, other actual path and complement
quantum systems are summed. Original input correlations remain unrestricted.
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

/-- Every left record observation comes from the original classical child run. -/
lemma parallelClassical_observe_left {Result : Type} [Fintype Result]
    [DecidableEq Result] (read : first.run.Record → Result) :
    ((((parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.execute environment Reference input.state).mapClassical
        (fun record => read
          (((ContextEmbedding.alongUnion left right separate).store record.1).1,
            ((join.hidden record.2.1).1,
              (((ContextEmbedding.alongUnion left right separate).store record.2.2.1).1,
                record.2.2.2.1))))).reindex
          (S := left.register.prod
            ((ContextEmbedding.alongUnion left right separate).frame.register.prod Reference))
          ((ContextEmbedding.alongUnion left right separate).referenceBasis
            Reference)).forgetReferenceFrame =
      (first.run.execute
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference
        ((ContextEmbedding.alongUnion left right separate).localInput
          (join.leftInput input)).state).mapClassical read := by
  have projected := congrArg
    (fun current : ExecutionState first.run.Record (left.register.prod Reference) =>
      current.mapClassical read)
    (parallelClassical_execute_left (allowAllocation := allowAllocation)
      join separate first second environment input)
  dsimp only [ContextEmbedding.projectState, ContextEmbedding.split,
    selectServiceLeft, State.mapHistory] at projected
  simp only [← ExecutionState.forgetReferenceFrame_mapClassical,
    ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.executionState_mapClassical_comp] at projected
  refine Eq.trans ?_ projected
  apply congrArg (fun current : ExecutionState Result
      ((left.disjointUnion right separate).register.prod Reference) =>
    (current.reindex
      (S := left.register.prod
        ((ContextEmbedding.alongUnion left right separate).frame.register.prod Reference))
      ((ContextEmbedding.alongUnion left right separate).referenceBasis
            Reference)).forgetReferenceFrame)
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Every right record observation comes from the original classical child run. -/
lemma parallelClassical_observe_right {Result : Type} [Fintype Result]
    [DecidableEq Result] (read : second.run.Record → Result) :
    ((((parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.execute environment Reference input.state).mapClassical
        (fun record => read
          (((ContextEmbedding.alongUnionRight left right separate).store record.1).1,
            ((join.hidden record.2.1).2,
              (((ContextEmbedding.alongUnionRight left right separate).store record.2.2.1).1,
                record.2.2.2.2))))).reindex
          (S := right.register.prod
            ((ContextEmbedding.alongUnionRight left right separate).frame.register.prod Reference))
          ((ContextEmbedding.alongUnionRight left right separate).referenceBasis
            Reference)).forgetReferenceFrame =
      (second.run.execute
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
        ((ContextEmbedding.alongUnionRight left right separate).localInput
          (join.rightInput input)).state).mapClassical read := by
  have projected := congrArg
    (fun current : ExecutionState second.run.Record (right.register.prod Reference) =>
      current.mapClassical read)
    (parallelClassical_execute_right (allowAllocation := allowAllocation)
      join separate first second environment input)
  dsimp only [ContextEmbedding.projectState, ContextEmbedding.split,
    selectServiceRight, State.mapHistory] at projected
  simp only [← ExecutionState.forgetReferenceFrame_mapClassical,
    ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.executionState_mapClassical_comp] at projected
  refine Eq.trans ?_ projected
  apply congrArg (fun current : ExecutionState Result
      ((left.disjointUnion right separate).register.prod Reference) =>
    (current.reindex
      (S := right.register.prod
        ((ContextEmbedding.alongUnionRight left right separate).frame.register.prod Reference))
      ((ContextEmbedding.alongUnionRight left right separate).referenceBasis
            Reference)).forgetReferenceFrame)
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

/-- Every left record observation comes from the original quantum child run. -/
lemma parallelQuantum_observe_left {Result : Type} [Fintype Result]
    [DecidableEq Result] (read : first.run.Record → Result) :
    ((((parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.execute environment Reference input.state).mapClassical
        (fun record => read
          (((ContextEmbedding.alongUnion left right separate).store record.1).1,
            ((join.hidden record.2.1).1,
              (((ContextEmbedding.alongUnion left right separate).store record.2.2.1).1,
                record.2.2.2.1))))).reindex
          (S := left.register.prod
            ((ContextEmbedding.alongUnion left right separate).frame.register.prod Reference))
          ((ContextEmbedding.alongUnion left right separate).referenceBasis
            Reference)).forgetReferenceFrame =
      (first.run.execute
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference
        ((ContextEmbedding.alongUnion left right separate).localInput
          (join.leftInput input)).state).mapClassical read := by
  have projected := congrArg
    (fun current : ExecutionState first.run.Record (left.register.prod Reference) =>
      current.mapClassical read)
    (parallelQuantum_execute_left (allowAllocation := allowAllocation)
      join separate first second environment input)
  dsimp only [ContextEmbedding.projectState, ContextEmbedding.split,
    selectServiceLeft, State.mapHistory] at projected
  simp only [← ExecutionState.forgetReferenceFrame_mapClassical,
    ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.executionState_mapClassical_comp] at projected
  refine Eq.trans ?_ projected
  apply congrArg (fun current : ExecutionState Result
      ((left.disjointUnion right separate).register.prod Reference) =>
    (current.reindex
      (S := left.register.prod
        ((ContextEmbedding.alongUnion left right separate).frame.register.prod Reference))
      ((ContextEmbedding.alongUnion left right separate).referenceBasis
            Reference)).forgetReferenceFrame)
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Every right record observation comes from the original quantum child run. -/
lemma parallelQuantum_observe_right {Result : Type} [Fintype Result]
    [DecidableEq Result] (read : second.run.Record → Result) :
    ((((parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.execute environment Reference input.state).mapClassical
        (fun record => read
          (((ContextEmbedding.alongUnionRight left right separate).store record.1).1,
            ((join.hidden record.2.1).2,
              (((ContextEmbedding.alongUnionRight left right separate).store record.2.2.1).1,
                record.2.2.2.2))))).reindex
          (S := right.register.prod
            ((ContextEmbedding.alongUnionRight left right separate).frame.register.prod Reference))
          ((ContextEmbedding.alongUnionRight left right separate).referenceBasis
            Reference)).forgetReferenceFrame =
      (second.run.execute
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
        ((ContextEmbedding.alongUnionRight left right separate).localInput
          (join.rightInput input)).state).mapClassical read := by
  have projected := congrArg
    (fun current : ExecutionState second.run.Record (right.register.prod Reference) =>
      current.mapClassical read)
    (parallelQuantum_execute_right (allowAllocation := allowAllocation)
      join separate first second environment input)
  dsimp only [ContextEmbedding.projectState, ContextEmbedding.split,
    selectServiceRight, State.mapHistory] at projected
  simp only [← ExecutionState.forgetReferenceFrame_mapClassical,
    ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.executionState_mapClassical_comp] at projected
  refine Eq.trans ?_ projected
  apply congrArg (fun current : ExecutionState Result
      ((left.disjointUnion right separate).register.prod Reference) =>
    (current.reindex
      (S := right.register.prod
        ((ContextEmbedding.alongUnionRight left right separate).frame.register.prod Reference))
      ((ContextEmbedding.alongUnionRight left right separate).referenceBasis
            Reference)).forgetReferenceFrame)
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end Quantum

end

end QuantumAlg.Algorithm

