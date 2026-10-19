/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.Composition
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Composition.Parallel.Observation
import all QuantumAlg.Core.Execution.Borrowed.Support
import all QuantumAlg.Core.Execution.State.Marginal.Reference

/-!
# Actual parallel final-state and path marginals

Each final local Store retains its full original-reference state. A child's
path block sums all actual opposite paths; thus every supported pair supplies
a supported path of each original child on its original local input.
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

/-- Each left path block is the exact marginal of the actual parallel path-pair blocks. -/
lemma parallelClassical_pathState_left :
    ((((parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.pathState environment Reference input.state).mapClassical
        (fun path => path.1)).reindex
          (S := left.register.prod
            ((ContextEmbedding.alongUnion left right separate).frame.register.prod Reference))
          ((ContextEmbedding.alongUnion left right separate).referenceBasis
            Reference)).forgetReferenceFrame =
      first.run.pathState
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference
        ((ContextEmbedding.alongUnion left right separate).localInput
          (join.leftInput input)).state := by
  unfold AlgorithmRun.pathState
  rw [ExecutionState.executionState_mapClassical_comp]
  exact parallelClassical_observe_left join separate first second environment input
    (fun record => record.2.2.2)

/-- A supported actual pair supplies a supported original left child path. -/
lemma parallelClassical_supports_left
    (path : (parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.code.Path)
    (supported : (parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.Supports environment Reference input.state path) :
    first.run.Supports
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference
      ((ContextEmbedding.alongUnion left right separate).localInput
        (join.leftInput input)).state path.1 := by
  unfold AlgorithmRun.Supports AlgorithmRun.pathMass
  rw [← parallelClassical_pathState_left (allowAllocation := allowAllocation)
    join separate first second environment input]
  rw [ExecutionState.forgetReferenceFrame_block_mass, ExecutionState.reindex_block_mass]
  exact (ExecutionState.mapClassical_block_mass_pos_iff
    ((parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.pathState environment Reference input.state)
    (fun pair => pair.1) path.1).mpr ⟨path, rfl, supported⟩

/-- The complete final left subsystem equals the original child's final state. -/
lemma parallelClassical_finalState_left :
    ((((parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.finalState environment Reference input.state).mapClassical
        (fun store => ((ContextEmbedding.alongUnion left right separate).store store).1)).reindex
          (S := left.register.prod
            ((ContextEmbedding.alongUnion left right separate).frame.register.prod Reference))
          ((ContextEmbedding.alongUnion left right separate).referenceBasis
            Reference)).forgetReferenceFrame =
      first.run.finalState
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference
        ((ContextEmbedding.alongUnion left right separate).localInput
          (join.leftInput input)).state := by
  unfold AlgorithmRun.finalState
  rw [ExecutionState.executionState_mapClassical_comp]
  exact parallelClassical_observe_left join separate first second environment input Prod.fst

/-- Each right path block is the exact marginal of the actual parallel path-pair blocks. -/
lemma parallelClassical_pathState_right :
    ((((parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.pathState environment Reference input.state).mapClassical
        (fun path => path.2)).reindex
          (S := right.register.prod
            ((ContextEmbedding.alongUnionRight left right separate).frame.register.prod Reference))
          ((ContextEmbedding.alongUnionRight left right separate).referenceBasis
            Reference)).forgetReferenceFrame =
      second.run.pathState
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
        ((ContextEmbedding.alongUnionRight left right separate).localInput
          (join.rightInput input)).state := by
  unfold AlgorithmRun.pathState
  rw [ExecutionState.executionState_mapClassical_comp]
  exact parallelClassical_observe_right join separate first second environment input
    (fun record => record.2.2.2)

/-- A supported actual pair supplies a supported original right child path. -/
lemma parallelClassical_supports_right
    (path : (parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.code.Path)
    (supported : (parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.Supports environment Reference input.state path) :
    second.run.Supports
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
      ((ContextEmbedding.alongUnionRight left right separate).localInput
        (join.rightInput input)).state path.2 := by
  unfold AlgorithmRun.Supports AlgorithmRun.pathMass
  rw [← parallelClassical_pathState_right (allowAllocation := allowAllocation)
    join separate first second environment input]
  rw [ExecutionState.forgetReferenceFrame_block_mass, ExecutionState.reindex_block_mass]
  exact (ExecutionState.mapClassical_block_mass_pos_iff
    ((parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.pathState environment Reference input.state)
    (fun pair => pair.2) path.2).mpr ⟨path, rfl, supported⟩

/-- The complete final right subsystem equals the original child's final state. -/
lemma parallelClassical_finalState_right :
    ((((parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.finalState environment Reference input.state).mapClassical
        (fun store =>
          ((ContextEmbedding.alongUnionRight left right separate).store store).1)).reindex
          (S := right.register.prod
            ((ContextEmbedding.alongUnionRight left right separate).frame.register.prod Reference))
          ((ContextEmbedding.alongUnionRight left right separate).referenceBasis
            Reference)).forgetReferenceFrame =
      second.run.finalState
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
        ((ContextEmbedding.alongUnionRight left right separate).localInput
          (join.rightInput input)).state := by
  unfold AlgorithmRun.finalState
  rw [ExecutionState.executionState_mapClassical_comp]
  exact parallelClassical_observe_right join separate first second environment input Prod.fst

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

/-- Each left path block is the exact marginal of the actual parallel path-pair blocks. -/
lemma parallelQuantum_pathState_left :
    ((((parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.pathState environment Reference input.state).mapClassical
        (fun path => path.1)).reindex
          (S := left.register.prod
            ((ContextEmbedding.alongUnion left right separate).frame.register.prod Reference))
          ((ContextEmbedding.alongUnion left right separate).referenceBasis
            Reference)).forgetReferenceFrame =
      first.run.pathState
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference
        ((ContextEmbedding.alongUnion left right separate).localInput
          (join.leftInput input)).state := by
  unfold AlgorithmRun.pathState
  rw [ExecutionState.executionState_mapClassical_comp]
  exact parallelQuantum_observe_left join separate first second environment input
    (fun record => record.2.2.2)

/-- A supported actual pair supplies a supported original left child path. -/
lemma parallelQuantum_supports_left
    (path : (parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.code.Path)
    (supported : (parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.Supports environment Reference input.state path) :
    first.run.Supports
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference
      ((ContextEmbedding.alongUnion left right separate).localInput
        (join.leftInput input)).state path.1 := by
  unfold AlgorithmRun.Supports AlgorithmRun.pathMass
  rw [← parallelQuantum_pathState_left (allowAllocation := allowAllocation)
    join separate first second environment input]
  rw [ExecutionState.forgetReferenceFrame_block_mass, ExecutionState.reindex_block_mass]
  exact (ExecutionState.mapClassical_block_mass_pos_iff
    ((parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.pathState environment Reference input.state)
    (fun pair => pair.1) path.1).mpr ⟨path, rfl, supported⟩

/-- The complete final left subsystem equals the original child's final state. -/
lemma parallelQuantum_finalState_left :
    ((((parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.finalState environment Reference input.state).mapClassical
        (fun store => ((ContextEmbedding.alongUnion left right separate).store store).1)).reindex
          (S := left.register.prod
            ((ContextEmbedding.alongUnion left right separate).frame.register.prod Reference))
          ((ContextEmbedding.alongUnion left right separate).referenceBasis
            Reference)).forgetReferenceFrame =
      first.run.finalState
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference
        ((ContextEmbedding.alongUnion left right separate).localInput
          (join.leftInput input)).state := by
  unfold AlgorithmRun.finalState
  rw [ExecutionState.executionState_mapClassical_comp]
  exact parallelQuantum_observe_left join separate first second environment input Prod.fst

/-- Each right path block is the exact marginal of the actual parallel path-pair blocks. -/
lemma parallelQuantum_pathState_right :
    ((((parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.pathState environment Reference input.state).mapClassical
        (fun path => path.2)).reindex
          (S := right.register.prod
            ((ContextEmbedding.alongUnionRight left right separate).frame.register.prod Reference))
          ((ContextEmbedding.alongUnionRight left right separate).referenceBasis
            Reference)).forgetReferenceFrame =
      second.run.pathState
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
        ((ContextEmbedding.alongUnionRight left right separate).localInput
          (join.rightInput input)).state := by
  unfold AlgorithmRun.pathState
  rw [ExecutionState.executionState_mapClassical_comp]
  exact parallelQuantum_observe_right join separate first second environment input
    (fun record => record.2.2.2)

/-- A supported actual pair supplies a supported original right child path. -/
lemma parallelQuantum_supports_right
    (path : (parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.code.Path)
    (supported : (parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.Supports environment Reference input.state path) :
    second.run.Supports
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
      ((ContextEmbedding.alongUnionRight left right separate).localInput
        (join.rightInput input)).state path.2 := by
  unfold AlgorithmRun.Supports AlgorithmRun.pathMass
  rw [← parallelQuantum_pathState_right (allowAllocation := allowAllocation)
    join separate first second environment input]
  rw [ExecutionState.forgetReferenceFrame_block_mass, ExecutionState.reindex_block_mass]
  exact (ExecutionState.mapClassical_block_mass_pos_iff
    ((parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.pathState environment Reference input.state)
    (fun pair => pair.2) path.2).mpr ⟨path, rfl, supported⟩

/-- The complete final right subsystem equals the original child's final state. -/
lemma parallelQuantum_finalState_right :
    ((((parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.finalState environment Reference input.state).mapClassical
        (fun store =>
          ((ContextEmbedding.alongUnionRight left right separate).store store).1)).reindex
          (S := right.register.prod
            ((ContextEmbedding.alongUnionRight left right separate).frame.register.prod Reference))
          ((ContextEmbedding.alongUnionRight left right separate).referenceBasis
            Reference)).forgetReferenceFrame =
      second.run.finalState
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference
        ((ContextEmbedding.alongUnionRight left right separate).localInput
          (join.rightInput input)).state := by
  unfold AlgorithmRun.finalState
  rw [ExecutionState.executionState_mapClassical_comp]
  exact parallelQuantum_observe_right join separate first second environment input Prod.fst

end Quantum

end

end QuantumAlg.Algorithm

