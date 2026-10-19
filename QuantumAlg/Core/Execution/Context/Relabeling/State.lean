/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Relabeling.Store
import all QuantumAlg.Core.Execution.Context.Relabeling.Layout
import all QuantumAlg.Core.Execution.State.Coordinate.Transport
import all QuantumAlg.Core.Execution.State.History
import all QuantumAlg.Core.Execution.Classical.Branch

/-!
# Complete state coordinates under injective placement

These proof coordinates preserve every classical block and the full quantum
matrix jointly with an arbitrary reference. The coordinate map follows the
prescribed physical and storage embeddings while retaining every original role
and value. It supplies no prepared state or runtime operation.
-/

namespace QuantumAlg.Execution.ContextRelabeling

noncomputable section

open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {source : RuntimeCtx kind}
  (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)

/-- Change only the runtime wire coordinates, retaining the full external reference. -/
def referenceBasis (Reference : Register) :
    (Register.prod source.register Reference).Index ≃
      (Register.prod (source.relabel keys physical).register Reference).Index :=
  (basis source keys physical).prodCongr (Equiv.refl Reference.Index)

/-- Retain the entire actual store and the original history in bijective coordinates. -/
def recordEquiv (History : Type) :
    (Store source × History) ≃ (Store (source.relabel keys physical) × History) :=
  (storeEquiv keys physical source).prodCongr (Equiv.refl History)

variable {Reference : Register} {H K : Type} [Fintype H] [Fintype K]

/-- Express the complete original state in the corresponding mapped coordinates. -/
def state (original : State source Reference H) :
    State (source.relabel keys physical) Reference H :=
  (original.mapClassical (recordEquiv (source := source) keys physical H)).reindex
    (referenceBasis (source := source) keys physical Reference)

/-- The reverse bijections recover every original classical block and matrix entry. -/
lemma state_inverse (original : State source Reference H) :
    (((state keys physical original).mapClassical
      (recordEquiv (source := source) keys physical H).symm).reindex
      (referenceBasis (source := source) keys physical Reference).symm) = original :=
  ExecutionState.coordinate_transport_inverse original
    (recordEquiv (source := source) keys physical H)
    (referenceBasis (source := source) keys physical Reference)

/-- The inverse store and basis coordinates assemble back to the supplied target state. -/
lemma state_reverse (target : State (source.relabel keys physical) Reference H) :
    state keys physical
      ((target.mapClassical
        (recordEquiv (source := source) keys physical H).symm).reindex
          (referenceBasis (source := source) keys physical Reference).symm) = target := by
  let labels := recordEquiv (source := source) keys physical H
  let coordinates := referenceBasis (source := source) keys physical Reference
  change (((target.mapClassical labels.symm).reindex coordinates.symm).mapClassical
    labels).reindex coordinates = target
  simpa only [Equiv.symm_symm] using
    (ExecutionState.coordinate_transport_inverse target labels.symm coordinates.symm)

/-- Every complete target state comes from one state in the original coordinates. -/
lemma state_surjective (target : State (source.relabel keys physical) Reference H) :
    ∃ original : State source Reference H, state keys physical original = target :=
  ⟨(target.mapClassical
    (recordEquiv (source := source) keys physical H).symm).reindex
      (referenceBasis (source := source) keys physical Reference).symm,
    state_reverse keys physical target⟩

/-- Each transported matrix entry is exactly the original entry at the inverse coordinates. -/
lemma state_entry (original : State source Reference H)
    (label : Store (source.relabel keys physical) × H)
    (row column : (Register.prod (source.relabel keys physical).register Reference).Index) :
    ((state keys physical original).block label).matrix row column =
      (original.block ((recordEquiv (source := source) keys physical H).symm label)).matrix
        ((referenceBasis (source := source) keys physical Reference).symm row)
        ((referenceBasis (source := source) keys physical Reference).symm column) :=
  ExecutionState.coordinate_transport_entry original
    (recordEquiv (source := source) keys physical H)
    (referenceBasis (source := source) keys physical Reference) label row column

/-- Total mass is unchanged, including for subnormalized or impossible branches. -/
lemma state_mass (original : State source Reference H) :
    (state keys physical original).mass = original.mass :=
  (ExecutionState.reindex_mass _ (referenceBasis (source := source) keys physical Reference)).trans
    (ExecutionState.mapClassical_mass original (recordEquiv (source := source) keys physical H))

/-- Changing the mathematical history commutes with the complete state coordinates. -/
lemma state_mapHistory (original : State source Reference H) (update : H → K) :
    state keys physical (original.mapHistory update) =
      (state keys physical original).mapHistory update := by
  let coordinates := referenceBasis (source := source) keys physical Reference
  let before := recordEquiv (source := source) keys physical H
  let after := recordEquiv (source := source) keys physical K
  let sourceMap := fun record : Store source × H => (record.1, update record.2)
  let targetMap := fun record : Store (source.relabel keys physical) × H =>
    (record.1, update record.2)
  have first := ExecutionState.executionState_mapClassical_comp original sourceMap after
  have second := ExecutionState.executionState_mapClassical_comp original before targetMap
  have commute := ExecutionState.coordinate_reindex_mapClassical
    (original.mapClassical before) coordinates targetMap
  have diagram : after ∘ sourceMap = targetMap ∘ before := rfl
  have combined := (congrArg (fun value => value.reindex coordinates) first).trans
    ((congrArg (fun labels => (original.mapClassical labels).reindex coordinates) diagram).trans
      ((congrArg (fun value => value.reindex coordinates) second.symm).trans commute.symm))
  convert combined using 1 <;>
    dsimp only [state, State.mapHistory, coordinates, before, after, sourceMap, targetMap]

/-- The stored-value branch selects exactly the same original classical fiber. -/
lemma state_selectClassical (original : State source Reference H)
    {shape : CShape} (ref : CInputRef source shape) (selected : shape.Value) :
    state keys physical (original.selectClassical (fun record => record.1.read ref) selected) =
      (state keys physical original).selectClassical
        (fun record => record.1.read (input keys physical ref)) selected := by
  apply ExecutionState.ext
  rintro ⟨stored, history⟩
  apply DensityOperator.ext
  ext row column
  rw [state_entry]
  change ((original.selectClassical (fun record => record.1.read ref) selected).block
    ((storeEquiv keys physical source).symm stored, history)).matrix
      ((referenceBasis (source := source) keys physical Reference).symm row)
      ((referenceBasis (source := source) keys physical Reference).symm column) = _
  have reads : ((storeEquiv keys physical source).symm stored).read ref =
      stored.read (input keys physical ref) := by
    have read := store_read_input keys physical ((storeEquiv keys physical source).symm stored) ref
    rw [(storeEquiv keys physical source).apply_symm_apply] at read
    exact read.symm
  simp only [ExecutionState.selectClassical_block, apply_ite DensityOperator.matrix,
    Matrix.ite_apply, DensityOperator.zero_matrix, Matrix.zero_apply, reads]
  by_cases active : stored.read (input keys physical ref) = selected
  · simp only [active, if_true]
    exact (state_entry keys physical original (stored, history) row column).symm
  · simp only [active, if_false]

/-- Admissible sums retain all classical fibers and all joint matrix entries. -/
lemma state_finiteSum {I : Type} [Fintype I]
    (original : I → State source Reference H) (total : ∑ index, (original index).mass ≤ 1) :
    state keys physical (ExecutionState.finiteSum original total) =
      ExecutionState.finiteSum (fun index => state keys physical (original index))
        (by simpa only [state_mass] using total) := by
  apply ExecutionState.ext
  intro label
  apply DensityOperator.ext
  ext row column
  rw [state_entry]
  simp only [ExecutionState.finiteSum_block_matrix, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun index _ =>
    (state_entry keys physical (original index) label row column).symm

end

end QuantumAlg.Execution.ContextRelabeling
