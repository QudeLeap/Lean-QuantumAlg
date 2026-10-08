/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Union.State
import all QuantumAlg.Core.Execution.State.History
import all QuantumAlg.Core.Execution.Classical.Branch

/-!
# Exact frame coordinates through history and classical selection

The complete right store remains part of every block label. Changing the
mathematical history, selecting an actual left read, and adding admissible
branches all commute with the same inverse store and quantum coordinates.
These statements concern complete density blocks, including arbitrary
correlations with the physically present frame [dW19, qcnotes.tex:5381,5394].
-/

namespace QuantumAlg.Execution.ContextUnion

noncomputable section

open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} (left right : RuntimeCtx kind)
  (separate : RuntimeCtx.StorageDisjoint left right)
  {Reference : Register} {H K : Type} [Fintype H] [Fintype K]

/-- Exact frame coordinates preserve the total mass of an arbitrary input state. -/
theorem contextUnion_splitState_mass
    (state : State (left.disjointUnion right separate) Reference H) :
    (splitState left right separate state).mass = state.mass :=
  (ExecutionState.reindex_mass _ (referenceBasis left right separate Reference)).trans
    (ExecutionState.mapClassical_mass state (recordEquiv left right separate H))

/-- A history map leaves the complete right-store label unchanged. -/
theorem contextUnion_splitState_mapHistory
    (state : State (left.disjointUnion right separate) Reference H) (update : H → K) :
    splitState left right separate (state.mapHistory update) =
      (splitState left right separate state).mapHistory
        (fun record => (record.1, update record.2)) := by
  let basis := referenceBasis left right separate Reference
  let inputLabels := recordEquiv left right separate H
  let outputLabels := recordEquiv left right separate K
  let sourceMap := fun record : Store (left.disjointUnion right separate) × H =>
    (record.1, update record.2)
  let resultMap := fun record : Store left × (Store right × H) =>
    (record.1, (record.2.1, update record.2.2))
  have source := ExecutionState.executionState_mapClassical_comp state sourceMap outputLabels
  have target := ExecutionState.executionState_mapClassical_comp state inputLabels resultMap
  have commute := ExecutionState.coordinate_reindex_mapClassical
    (state.mapClassical inputLabels) basis resultMap
  have diagram : outputLabels ∘ sourceMap = resultMap ∘ inputLabels := by
    rfl
  have combined := (congrArg (fun original => original.reindex basis) source).trans
    ((congrArg (fun labels => (state.mapClassical labels).reindex basis) diagram).trans
      ((congrArg (fun original => original.reindex basis) target.symm).trans commute.symm))
  convert combined using 1 <;>
    dsimp only [splitState, State.mapHistory, basis, inputLabels, outputLabels,
      sourceMap, resultMap];
    congr! 2

/-- The identity instruction records Unit while retaining the separate right store. -/
theorem contextUnion_splitState_skip
    (state : State (left.disjointUnion right separate) Reference H) :
    splitState left right separate state.skip =
      (splitState left right separate state).skip.mapHistory
        (fun record => (record.1.1, (record.1.2, record.2))) := by
  exact (contextUnion_splitState_mapHistory left right separate state
    (fun history => (history, ()))).trans
      (State.mapHistory_comp (splitState left right separate state)
        (fun history => (history, ()))
        (fun record => (record.1.1, (record.1.2, record.2)))).symm

/-- The actual lifted read selects the same left fiber, retaining every right-store value. -/
theorem contextUnion_splitState_selectClassical
    (state : State (left.disjointUnion right separate) Reference H)
    {shape : CShape} (input : CInputRef left shape) (selected : shape.Value) :
    splitState left right separate
        (state.selectClassical (fun record => record.1.read (inputLeft separate input)) selected) =
      (splitState left right separate state).selectClassical
        (fun record => record.1.read input) selected := by
  apply ExecutionState.ext
  rintro ⟨first, second, history⟩
  apply DensityOperator.ext
  ext row column
  rw [contextUnion_splitState_entry]
  change ((state.selectClassical
      (fun record => record.1.read (inputLeft separate input)) selected).block
        (join separate first second, history)).matrix
          ((referenceBasis left right separate Reference).symm row)
          ((referenceBasis left right separate Reference).symm column) = _
  simp only [ExecutionState.selectClassical_block, apply_ite DensityOperator.matrix,
    Matrix.ite_apply, DensityOperator.zero_matrix, Matrix.zero_apply,
    contextUnion_read_join_left]
  by_cases active : first.read input = selected
  · simp only [active, if_true]
    exact (contextUnion_splitState_entry left right separate state
      (first, (second, history)) row column).symm
  · simp only [active, if_false]

/-- Admissible sums preserve every right-store fiber and every complete matrix entry. -/
theorem contextUnion_splitState_finiteSum {I : Type} [Fintype I]
    (states : I → State (left.disjointUnion right separate) Reference H)
    (total : ∑ index, (states index).mass ≤ 1) :
    splitState left right separate (ExecutionState.finiteSum states total) =
      ExecutionState.finiteSum (fun index => splitState left right separate (states index))
        (by simpa only [contextUnion_splitState_mass] using total) := by
  apply ExecutionState.ext
  intro label
  apply DensityOperator.ext
  ext row column
  rw [contextUnion_splitState_entry]
  simp only [ExecutionState.finiteSum_block_matrix, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun index _ =>
    (contextUnion_splitState_entry left right separate (states index) label row column).symm

variable {Hidden : Type} [Fintype Hidden]

/-- Separating a resident frame preserves total mass and the persistent service. -/
theorem contextUnion_splitServiceState_mass
    (state : State (left.disjointUnion right separate) Reference (Hidden × H)) :
    (splitServiceState left right separate state).mass = state.mass := by
  rw [splitServiceState, State.mapHistory_mass, contextUnion_splitState_mass]

/-- Updating ordinary history leaves the service and complete resident store in place. -/
theorem contextUnion_splitServiceState_mapHistory
    (state : State (left.disjointUnion right separate) Reference (Hidden × H)) (update : H → K) :
    splitServiceState left right separate
        (state.mapHistory (fun record => (record.1, update record.2))) =
      (splitServiceState left right separate state).mapHistory
        (fun record => (record.1, (record.2.1, update record.2.2))) := by
  dsimp only [splitServiceState]
  rw [contextUnion_splitState_mapHistory]
  simp only [State.mapHistory_comp, Function.comp_def]
  rfl

/-- A stored-value branch selects the same fiber with the service label retained. -/
theorem contextUnion_splitServiceState_selectClassical
    (state : State (left.disjointUnion right separate) Reference (Hidden × H))
    {shape : CShape} (input : CInputRef left shape) (selected : shape.Value) :
    splitServiceState left right separate
        (state.selectClassical (fun record => record.1.read (inputLeft separate input)) selected) =
      (splitServiceState left right separate state).selectClassical
        (fun record => record.1.read input) selected := by
  dsimp only [splitServiceState]
  rw [contextUnion_splitState_selectClassical, State.mapHistory_selectClassical]

/-- Finite branch sums preserve every service and resident-store correlation. -/
theorem contextUnion_splitServiceState_finiteSum {I : Type} [Fintype I]
    (states : I → State (left.disjointUnion right separate) Reference (Hidden × H))
    (total : ∑ index, (states index).mass ≤ 1) :
    splitServiceState left right separate (ExecutionState.finiteSum states total) =
      ExecutionState.finiteSum (fun index => splitServiceState left right separate (states index))
        (by simpa only [contextUnion_splitServiceState_mass] using total) := by
  dsimp only [splitServiceState]
  rw [contextUnion_splitState_finiteSum]
  convert (ExecutionState.mapClassical_finiteSum
    (fun index => splitState left right separate (states index))
    (by simpa only [contextUnion_splitState_mass] using total)
    (fun record => (record.1, serviceHistory right Hidden H record.2))) using 1 <;>
    dsimp only [State.mapHistory] <;>
    congr! 2
  apply ExecutionState.ext
  intro label
  apply DensityOperator.ext
  simp only [ExecutionState.finiteSum, ExecutionState.mapClassical_block_matrix]
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr rfl
  intro entry _
  split_ifs <;> rfl

end

end QuantumAlg.Execution.ContextUnion
