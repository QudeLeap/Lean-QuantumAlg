/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Context.Embedding.Selection.Values
import all QuantumAlg.Core.Execution.Context.Embedding.Selection
import all QuantumAlg.Core.Execution.Context.Embedding.Selection.Values
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Prod

/-!
# The exact complement of physically placed output wires

The complement consists of the original unselected local wires and every
unchanged frame wire. Their basis correspondence preserves each native value
on its actual physical system. Full-state reassembly therefore commutes with
the selected/complement split [dW19, qcnotes.tex:389,6827].
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller)

/-- A local placed position is selected precisely when the original position is selected. -/
lemma contextEmbedding_selection_local_iff
    (selected : Finset (Fin localCtx.systemCount)) (index : Fin localCtx.systemCount) :
    placement.position index ∈ placement.selection selected ↔ index ∈ selected :=
  Finset.mem_map' placement.position

/-- Every frame wire lies outside a selection made solely of original local wires. -/
lemma contextEmbedding_selection_frame_not_mem
    (selected : Finset (Fin localCtx.systemCount)) (index : Fin placement.frame.systemCount) :
    placement.positions (.inr index) ∉ placement.selection selected := by
  intro member
  obtain ⟨localIndex, _, same⟩ := Finset.mem_map.mp member
  have impossible := placement.positions.injective same
  cases impossible

/-- Unselected local positions and all frame positions partition the caller complement. -/
def complementPositions (selected : Finset (Fin localCtx.systemCount)) :
    QuantumLayout.SelectedPosition selectedᶜ ⊕ Fin placement.frame.systemCount ≃
      QuantumLayout.SelectedPosition (placement.selection selected)ᶜ :=
  ((Equiv.refl (QuantumLayout.SelectedPosition selectedᶜ)).sumCongr
    (Equiv.subtypeUnivEquiv (p := fun _ : Fin placement.frame.systemCount => True)
      (fun _ => True.intro)).symm).trans
      ((Equiv.subtypeSum (p := fun index :
        Fin localCtx.systemCount ⊕ Fin placement.frame.systemCount =>
        match index with
        | .inl localIndex => localIndex ∈ selectedᶜ
        | .inr _ => True)).symm.trans
          (placement.positions.subtypeEquiv
            (p := fun index : Fin localCtx.systemCount ⊕ Fin placement.frame.systemCount =>
              match index with
              | .inl localIndex => localIndex ∈ selectedᶜ
              | .inr _ => True)
            (q := fun index : Fin caller.systemCount =>
              index ∈ (placement.selection selected)ᶜ) fun index => by
            cases index with
            | inl index =>
                change index ∈ selectedᶜ ↔ placement.position index ∈
                  (placement.selection selected)ᶜ
                simpa only [Finset.mem_compl] using
                  not_congr (placement.contextEmbedding_selection_local_iff selected index).symm
            | inr index =>
                exact iff_of_true True.intro (Finset.mem_compl.mpr
                  (placement.contextEmbedding_selection_frame_not_mem selected index))))

private def complementValueType (selected : Finset (Fin localCtx.systemCount)) :
    QuantumLayout.SelectedPosition selectedᶜ ⊕ Fin placement.frame.systemCount → Type
  | .inl index => Fin (localCtx.quantumLayout.wire index.val).dimension
  | .inr index => Fin (placement.frame.quantumLayout.wire index).dimension

private def complementValueEquiv (selected : Finset (Fin localCtx.systemCount))
    (index : QuantumLayout.SelectedPosition selectedᶜ ⊕ Fin placement.frame.systemCount) :
    placement.complementValueType selected index ≃
      Fin (caller.quantumLayout.wire
        (placement.complementPositions selected index).val).dimension :=
  match index with
  | .inl index => finCongr (congrArg PNat.val
      (placement.contextEmbedding_position_dimension index.val).symm)
  | .inr index => finCongr (congrArg (fun wire : QuantumWire => (wire.dimension : Nat))
      (placement.contextEmbedding_frame_position_wire index).symm)

/-- The caller complement retains the original local complement and entire frame basis. -/
def complementBasis (selected : Finset (Fin localCtx.systemCount)) :
    localCtx.quantumLayout.ComplementBasis selected × placement.frame.register.Index ≃
      caller.quantumLayout.ComplementBasis (placement.selection selected) :=
  (Equiv.sumPiEquivProdPi (placement.complementValueType selected)).symm.trans
    ((placement.complementPositions selected).piCongr (placement.complementValueEquiv selected))

/-- Every unselected local finite value reaches the same actual physical wire. -/
lemma contextEmbedding_complementBasis_local_value
    (selected : Finset (Fin localCtx.systemCount))
    (localValue : localCtx.quantumLayout.ComplementBasis selected)
    (frameValue : placement.frame.register.Index)
    (index : QuantumLayout.SelectedPosition selectedᶜ) :
    (placement.complementBasis selected (localValue, frameValue)
      (placement.complementPositions selected (.inl index))).val = (localValue index).val := by
  exact congrArg
    (fun value : Fin (caller.quantumLayout.wire
      (placement.complementPositions selected (.inl index)).val).dimension => value.val)
    (Equiv.piCongr_apply_apply
      (W := placement.complementValueType selected)
      (Z := fun position : QuantumLayout.SelectedPosition (placement.selection selected)ᶜ =>
        Fin (caller.quantumLayout.wire position.val).dimension)
      (placement.complementPositions selected) (placement.complementValueEquiv selected)
      ((Equiv.sumPiEquivProdPi (placement.complementValueType selected)).symm
        (localValue, frameValue)) (.inl index))

/-- Every complete frame finite value remains on its unchanged physical wire. -/
lemma contextEmbedding_complementBasis_frame_value
    (selected : Finset (Fin localCtx.systemCount))
    (localValue : localCtx.quantumLayout.ComplementBasis selected)
    (frameValue : placement.frame.register.Index) (index : Fin placement.frame.systemCount) :
    (placement.complementBasis selected (localValue, frameValue)
      (placement.complementPositions selected (.inr index))).val = (frameValue index).val := by
  exact congrArg
    (fun value : Fin (caller.quantumLayout.wire
      (placement.complementPositions selected (.inr index)).val).dimension => value.val)
    (Equiv.piCongr_apply_apply
      (W := placement.complementValueType selected)
      (Z := fun position : QuantumLayout.SelectedPosition (placement.selection selected)ᶜ =>
        Fin (caller.quantumLayout.wire position.val).dimension)
      (placement.complementPositions selected) (placement.complementValueEquiv selected)
      ((Equiv.sumPiEquivProdPi (placement.complementValueType selected)).symm
        (localValue, frameValue)) (.inr index))

/-- Selection reassembly and the original complete physical placement commute exactly. -/
lemma contextEmbedding_joinSelectedBasis
    (selected : Finset (Fin localCtx.systemCount))
    (selectedValue : localCtx.quantumLayout.SelectedBasis selected)
    (complementValue : localCtx.quantumLayout.ComplementBasis selected)
    (frameValue : placement.frame.register.Index) :
    caller.quantumLayout.joinSelectedBasis (placement.selection selected)
      (placement.selectedBasis selected selectedValue)
      (placement.complementBasis selected (complementValue, frameValue)) =
    placement.basis.symm
      (localCtx.quantumLayout.joinSelectedBasis selected selectedValue complementValue,
        frameValue) := by
  funext index
  obtain ⟨original, rfl⟩ := placement.positions.surjective index
  apply Fin.ext
  cases original with
  | inl index =>
      change (caller.quantumLayout.joinSelectedBasis (placement.selection selected)
        (placement.selectedBasis selected selectedValue)
        (placement.complementBasis selected (complementValue, frameValue))
        (placement.position index)).val =
        (placement.basis.symm
          (localCtx.quantumLayout.joinSelectedBasis selected selectedValue complementValue,
            frameValue) (placement.position index)).val
      rw [placement.contextEmbedding_join_local_value]
      by_cases member : index ∈ selected
      · have left := congrArg Fin.val
          (caller.quantumLayout.joinSelectedBasis_selected_value _
            (placement.selectedBasis selected selectedValue)
            (placement.complementBasis selected (complementValue, frameValue))
            (placement.selectedPositions selected ⟨index, member⟩))
        have right := congrArg Fin.val
          (localCtx.quantumLayout.joinSelectedBasis_selected_value selected
            selectedValue complementValue ⟨index, member⟩)
        exact (left.trans (placement.contextEmbedding_selectedBasis_value selected
          selectedValue ⟨index, member⟩)).trans right.symm
      · let complementIndex : QuantumLayout.SelectedPosition selectedᶜ :=
          ⟨index, Finset.mem_compl.mpr member⟩
        have left := congrArg Fin.val
          (caller.quantumLayout.joinSelectedBasis_complement_value _
            (placement.selectedBasis selected selectedValue)
            (placement.complementBasis selected (complementValue, frameValue))
            (placement.complementPositions selected (.inl complementIndex)))
        have right := congrArg Fin.val
          (localCtx.quantumLayout.joinSelectedBasis_complement_value selected
            selectedValue complementValue complementIndex)
        exact (left.trans (placement.contextEmbedding_complementBasis_local_value selected
          complementValue frameValue complementIndex)).trans right.symm
  | inr index =>
      rw [placement.contextEmbedding_join_frame_value]
      have left := congrArg Fin.val
        (caller.quantumLayout.joinSelectedBasis_complement_value _
          (placement.selectedBasis selected selectedValue)
          (placement.complementBasis selected (complementValue, frameValue))
          (placement.complementPositions selected (.inr index)))
      exact left.trans (placement.contextEmbedding_complementBasis_frame_value selected
        complementValue frameValue index)

end

end QuantumAlg.ContextEmbedding
