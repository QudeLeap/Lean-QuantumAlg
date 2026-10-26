/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.OwnedLayoutView
import all QuantumAlg.Core.Execution.State.History
import all QuantumAlg.Core.Execution.State.History.Selection
import all QuantumAlg.Core.Execution.Reference.ClassicalTag.State
import all QuantumAlg.Core.Execution.Reference.Preservation
import all QuantumAlg.Core.Execution.Composition.ClassicalTag

/-!
# Exact state laws for scoped owned slices

The view retains all classical records and every physical quantum coordinate.
These equalities apply to complete states with arbitrary external references.
-/

namespace QuantumAlg.OwnedLayoutView

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {original viewed : RuntimeCtx .quantum} (view : OwnedLayoutView original viewed)
  {Reference : Register} {H K : Type} [Fintype H] [Fintype K]

/-- Changing the mathematical history commutes with the same complete state coordinates. -/
lemma split_mapHistory (state : State original Reference H) (update : H → K) :
    split view (state.mapHistory update) = (split view state).mapHistory update := by
  let coordinates := view.referenceBasis Reference
  let before := view.record H
  let after := view.record K
  let originalMap := fun record : Store original × H => (record.1, update record.2)
  let viewedMap := fun record : Store viewed × H => (record.1, update record.2)
  have first := ExecutionState.executionState_mapClassical_comp state originalMap after
  have second := ExecutionState.executionState_mapClassical_comp state before viewedMap
  have commute := ExecutionState.coordinate_reindex_mapClassical
    (state.mapClassical before) coordinates viewedMap
  have diagram : after ∘ originalMap = viewedMap ∘ before := rfl
  have combined := (congrArg (fun value => value.reindex coordinates) first).trans
    ((congrArg (fun labels => (state.mapClassical labels).reindex coordinates) diagram).trans
      ((congrArg (fun value => value.reindex coordinates) second.symm).trans commute.symm))
  convert combined using 1 <;>
    dsimp only [split, State.mapHistory, coordinates, before, after, originalMap, viewedMap]

/-- Restoring entry grouping commutes with every mathematical history map. -/
lemma join_mapHistory (state : State viewed Reference H) (update : H → K) :
    view.join (state.mapHistory update) = (view.join state).mapHistory update := by
  apply view.split_injective
  rw [view.split_join, view.split_mapHistory, view.split_join]

/-- Entering the view preserves every complete earlier-history fiber. -/
lemma split_selectHistory {D : Type} [DecidableEq D]
    (state : State original Reference H) (read : H → D) (selected : D) :
    view.split (state.selectHistory read selected) =
      (view.split state).selectHistory read selected := by
  apply ExecutionState.ext
  intro label
  apply DensityOperator.ext
  ext row column
  rw [view.split_entry]
  simp only [State.selectHistory, ExecutionState.selectClassical_block,
    apply_ite DensityOperator.matrix, Matrix.ite_apply, DensityOperator.zero_matrix,
    Matrix.zero_apply]
  change (if read label.2 = selected then
    (state.block ((view.record H).symm label)).matrix
      ((view.referenceBasis Reference).symm row)
      ((view.referenceBasis Reference).symm column) else 0) =
    (if read label.2 = selected then ((view.split state).block label).matrix row column else 0)
  by_cases active : read label.2 = selected
  · simp only [active, if_true]
    exact (view.split_entry state label row column).symm
  · simp only [active, if_false]

/-- Restoring the grouping retains the selected earlier-history fiber. -/
lemma join_selectHistory {D : Type} [DecidableEq D]
    (state : State viewed Reference H) (read : H → D) (selected : D) :
    view.join (state.selectHistory read selected) =
      (view.join state).selectHistory read selected := by
  apply view.split_injective
  rw [view.split_join, view.split_selectHistory, view.split_join]

/-- The same original external reference coordinates pass through the scoped split. -/
lemma split_reference {Other : Register} (basis : Reference.Index ≃ Other.Index)
    (state : State original Reference H) :
    view.split (state.reindex (S := original.register.prod Other)
      ((Equiv.refl original.register.Index).prodCongr basis)) =
      (view.split state).reindex (S := viewed.register.prod Other)
        ((Equiv.refl viewed.register.Index).prodCongr basis) := by
  unfold split
  rw [ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.reindex_trans, ExecutionState.reindex_trans]
  congr 1

/-- Restoring the grouping leaves every original reference coordinate unchanged. -/
lemma join_reference {Other : Register} (basis : Reference.Index ≃ Other.Index)
    (state : State viewed Reference H) :
    view.join (state.reindex (S := viewed.register.prod Other)
      ((Equiv.refl viewed.register.Index).prodCongr basis)) =
      (view.join state).reindex (S := original.register.prod Other)
        ((Equiv.refl original.register.Index).prodCongr basis) := by
  unfold join
  rw [ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.reindex_trans, ExecutionState.reindex_trans]
  congr 1

/-- Every diagonal external-tag slice is retained by the view. -/
lemma split_decodeReferenceTag {Tag : Register}
    (state : State original (Tag.prod Reference) H) :
    view.split (State.decodeReferenceTag state) =
      State.decodeReferenceTag (view.split state) := by
  apply ExecutionState.ext
  rintro ⟨stored, history, tag⟩
  apply DensityOperator.ext
  ext row column
  rw [view.split_entry, State.decodeReferenceTag_entry,
    State.decodeReferenceTag_entry, view.split_entry]
  rfl

/-- Diagonal external-tag slicing also commutes with restoring the grouping. -/
lemma join_decodeReferenceTag {Tag : Register}
    (state : State viewed (Tag.prod Reference) H) :
    view.join (State.decodeReferenceTag state) =
      State.decodeReferenceTag (view.join state) := by
  apply view.split_injective
  rw [view.split_join, view.split_decodeReferenceTag, view.split_join]

/-- Service and history tag coordinates commute with the exact view split. -/
lemma split_decodeOracleTag {Tag : Register} {Hidden : Type} [Fintype Hidden]
    (state : State original (Tag.prod Reference) (Hidden × H)) :
    view.split (State.decodeOracleTag state) = State.decodeOracleTag (view.split state) := by
  simp only [State.decodeOracleTag, view.split_mapHistory, view.split_decodeReferenceTag]

/-- Service, history and path tag coordinates commute with restoring the grouping. -/
lemma join_decodeExecutionTag {Tag : Register} {Hidden Path : Type}
    [Fintype Hidden] [Fintype Path]
    (state : State viewed (Tag.prod Reference) (Hidden × (H × Path))) :
    view.join (State.decodeExecutionTag state) = State.decodeExecutionTag (view.join state) := by
  simp only [State.decodeExecutionTag, State.decodeOracleTag,
    view.join_mapHistory, view.join_decodeReferenceTag]

private lemma referenceMarginal_reindex {C : Type} [Fintype C] {R S : Register}
    (state : ExecutionState C (R.prod Reference)) (basis : R.Index ≃ S.Index) :
    (state.reindex (S := S.prod Reference)
      (basis.prodCongr (Equiv.refl Reference.Index))).referenceMarginal =
        state.referenceMarginal := by
  apply DensityOperator.ext
  ext row column
  simp only [ExecutionState.referenceMarginal_entry, ExecutionState.quantumMarginal,
    Matrix.sum_apply, ExecutionState.reindex_block_entry]
  change (∑ coordinate : S.Index, ∑ label : C,
    (state.block label).matrix (basis.symm coordinate, row) (basis.symm coordinate, column)) = _
  exact basis.symm.sum_comp (fun coordinate : R.Index => ∑ label : C,
    (state.block label).matrix (coordinate, row) (coordinate, column))

/-- An owned-layout split preserves the complete external-reference marginal. -/
lemma split_referenceMarginal (state : State original Reference H) :
    (view.split state).referenceMarginal = state.referenceMarginal := by
  rw [split, referenceBasis, referenceMarginal_reindex,
    ExecutionState.mapClassical_referenceMarginal]

/-- Regrouping back preserves the same complete external-reference marginal. -/
lemma join_referenceMarginal (state : State viewed Reference H) :
    (view.join state).referenceMarginal = state.referenceMarginal := by
  have law := view.split_referenceMarginal (view.join state)
  rw [view.split_join] at law
  exact law.symm


end

end QuantumAlg.OwnedLayoutView
