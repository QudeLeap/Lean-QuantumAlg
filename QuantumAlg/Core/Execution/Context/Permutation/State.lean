/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Permutation.Store
import all QuantumAlg.Core.Execution.Context.Permutation.Layout
import all QuantumAlg.Core.Execution.State.Coordinate.Transport
import all QuantumAlg.Core.Execution.State.History
import all QuantumAlg.Core.Execution.Classical.Branch

/-!+# Complete state coordinates under entry permutation

These proof coordinates preserve every classical block and the full quantum
matrix jointly with an arbitrary reference. The permutation retains complete
entry identities and roles. It supplies no prepared state or runtime operation.
-/

namespace QuantumAlg.Execution.ContextPermutation

noncomputable section

open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {source target : RuntimeCtx kind}
  (same : source.entries.Perm target.entries)

/-- Change only the runtime wire coordinates, retaining the full external reference. -/
def referenceBasis (Reference : Register) :
    (Register.prod source.register Reference).Index ≃
      (Register.prod target.register Reference).Index :=
  (basis same).prodCongr (Equiv.refl Reference.Index)

/-- Retain the entire actual store and the original history in bijective coordinates. -/
def recordEquiv (History : Type) :
    (Store source × History) ≃ (Store target × History) :=
  (storeEquiv same).prodCongr (Equiv.refl History)

variable {Reference : Register} {H K : Type} [Fintype H] [Fintype K]

/-- Express the complete original state in the corresponding entry coordinates. -/
def state (original : State source Reference H) : State target Reference H :=
  (original.mapClassical (recordEquiv same H)).reindex (referenceBasis same Reference)

/-- The reverse bijections recover every original classical block and matrix entry. -/
theorem state_inverse (original : State source Reference H) :
    (((state same original).mapClassical (recordEquiv same H).symm).reindex
      (referenceBasis same Reference).symm) = original :=
  ExecutionState.coordinate_transport_inverse original (recordEquiv same H)
    (referenceBasis same Reference)

/-- Each transported matrix entry is exactly the original entry at the inverse coordinates. -/
theorem state_entry (original : State source Reference H) (label : Store target × H)
    (row column : (Register.prod target.register Reference).Index) :
    ((state same original).block label).matrix row column =
      (original.block ((recordEquiv same H).symm label)).matrix
        ((referenceBasis same Reference).symm row)
        ((referenceBasis same Reference).symm column) :=
  ExecutionState.coordinate_transport_entry original (recordEquiv same H)
    (referenceBasis same Reference) label row column

/-- Total mass is unchanged, including for subnormalized or impossible branches. -/
theorem state_mass (original : State source Reference H) :
    (state same original).mass = original.mass :=
  (ExecutionState.reindex_mass _ (referenceBasis same Reference)).trans
    (ExecutionState.mapClassical_mass original (recordEquiv same H))

/-- Changing the mathematical history commutes with the same complete state coordinates. -/
theorem state_mapHistory (original : State source Reference H) (update : H → K) :
    state same (original.mapHistory update) = (state same original).mapHistory update := by
  let coordinates := referenceBasis same Reference
  let before := recordEquiv same H
  let after := recordEquiv same K
  let sourceMap := fun record : Store source × H => (record.1, update record.2)
  let targetMap := fun record : Store target × H => (record.1, update record.2)
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
theorem state_selectClassical (original : State source Reference H)
    {shape : CShape} (ref : CInputRef source shape) (selected : shape.Value) :
    state same (original.selectClassical (fun record => record.1.read ref) selected) =
      (state same original).selectClassical
        (fun record => record.1.read (input same ref)) selected := by
  apply ExecutionState.ext
  rintro ⟨stored, history⟩
  apply DensityOperator.ext
  ext row column
  rw [state_entry]
  change ((original.selectClassical (fun record => record.1.read ref) selected).block
    (store same.symm stored, history)).matrix
      ((referenceBasis same Reference).symm row)
      ((referenceBasis same Reference).symm column) = _
  have reads : (store same.symm stored).read ref = stored.read (input same ref) := by
    have read := store_read_input same (store same.symm stored) ref
    rw [store_inverse same.symm] at read
    exact read.symm
  simp only [ExecutionState.selectClassical_block, apply_ite DensityOperator.matrix,
    Matrix.ite_apply, DensityOperator.zero_matrix, Matrix.zero_apply, reads]
  by_cases active : stored.read (input same ref) = selected
  · simp only [active, if_true]
    exact (state_entry same original (stored, history) row column).symm
  · simp only [active, if_false]

/-- Admissible sums retain all classical fibers and all joint matrix entries. -/
theorem state_finiteSum {I : Type} [Fintype I]
    (original : I → State source Reference H) (total : ∑ index, (original index).mass ≤ 1) :
    state same (ExecutionState.finiteSum original total) =
      ExecutionState.finiteSum (fun index => state same (original index))
        (by simpa only [state_mass] using total) := by
  apply ExecutionState.ext
  intro label
  apply DensityOperator.ext
  ext row column
  rw [state_entry]
  simp only [ExecutionState.finiteSum_block_matrix, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun index _ =>
    (state_entry same (original index) label row column).symm

end

end QuantumAlg.Execution.ContextPermutation
