/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Preparation.Borrowed.Positions
import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Base.Layout.Quantum.Selection

/-!
# Borrowed observation coordinates after preparation

The complementary basis is the product of the fresh basis and the original
complementary basis. Joining it with any fixed borrowed label agrees with
the actual preparation tensor map. This equality retains every individual
finite value and applies to heterogeneous local dimensions.
-/

namespace QuantumAlg.Execution.PreparationBorrowed

noncomputable section

variable {count : Nat} (ctx : RuntimeCtx .quantum) (key : StorageKey)
  (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
  (disjoint : List.Disjoint layout.identities ctx.physicalIdx)

private def complementValueEquiv
    (index : Fin count ⊕ QuantumLayout.SelectedPosition ctx.borrowedSelectionᶜ) :
    Sum.elim (fun position => Fin (layout.wire position).dimension)
      (fun position => Fin (ctx.quantumLayout.wire position.val).dimension) index ≃
        Fin ((ctx.addOwnedLayout key layout fresh disjoint).quantumLayout.wire
          (complementPositionEquiv ctx key layout fresh disjoint index).val).dimension := by
  cases index with
  | inl index =>
    exact finCongr (congrArg (fun dimension : ℕ+ => (dimension : Nat))
      (complementPositionEquiv_dimension ctx key layout fresh disjoint (.inl index)).symm)
  | inr index =>
    exact finCongr (congrArg (fun dimension : ℕ+ => (dimension : Nat))
      (complementPositionEquiv_dimension ctx key layout fresh disjoint (.inr index)).symm)

/-- Fresh and old complementary values together give exactly the new complement. -/
def complementBasisEquiv :
    (layout.Basis × ctx.quantumLayout.ComplementBasis ctx.borrowedSelection) ≃
      (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout.ComplementBasis
        (ctx.addOwnedLayout key layout fresh disjoint).borrowedSelection :=
  (Equiv.prodPiEquivSumPi (fun index => Fin (layout.wire index).dimension)
    (fun index : QuantumLayout.SelectedPosition ctx.borrowedSelectionᶜ =>
      Fin (ctx.quantumLayout.wire index.val).dimension)).trans
    (Equiv.piCongr (complementPositionEquiv ctx key layout fresh disjoint)
      (complementValueEquiv ctx key layout fresh disjoint))

/-- Complement assembly preserves the fresh values at their actual physical positions. -/
theorem complementBasisEquiv_new_value (newBasis : layout.Basis)
    (oldBasis : ctx.quantumLayout.ComplementBasis ctx.borrowedSelection) (index : Fin count) :
    (complementBasisEquiv ctx key layout fresh disjoint (newBasis, oldBasis)
      (complementPositionEquiv ctx key layout fresh disjoint (.inl index))).val =
        (newBasis index).val := by
  rw [complementBasisEquiv, Equiv.trans_apply, Equiv.piCongr_apply_apply]
  rfl

/-- Complement assembly preserves all original complementary values. -/
theorem complementBasisEquiv_old_value (newBasis : layout.Basis)
    (oldBasis : ctx.quantumLayout.ComplementBasis ctx.borrowedSelection)
    (index : QuantumLayout.SelectedPosition ctx.borrowedSelectionᶜ) :
    (complementBasisEquiv ctx key layout fresh disjoint (newBasis, oldBasis)
      (complementPositionEquiv ctx key layout fresh disjoint (.inr index))).val =
        (oldBasis index).val := by
  rw [complementBasisEquiv, Equiv.trans_apply, Equiv.piCongr_apply_apply]
  rfl

/-- An original selected position is selected at its same physical wire after preparation. -/
def borrowedPosition (index : QuantumLayout.SelectedPosition ctx.borrowedSelection) :
    QuantumLayout.SelectedPosition
      (ctx.addOwnedLayout key layout fresh disjoint).borrowedSelection :=
  ⟨fullPositionEquiv ctx key layout fresh disjoint (.inr index.val),
    (fullPositionEquiv_old_borrowed ctx key layout fresh disjoint index.val).mpr index.property⟩

/-- The common ordered borrowed frame assigns the same position before and after preparation. -/
theorem borrowedPosition_order (index : QuantumLayout.SelectedPosition ctx.borrowedSelection) :
    (ctx.addOwnedLayout key layout fresh disjoint).borrowedPositionEquiv
      (borrowedPosition ctx key layout fresh disjoint index) = ctx.borrowedPositionEquiv index := by
  apply ctx.borrowedQuantumLayout.identityInjective
  change ((ctx.addOwnedLayout key layout fresh disjoint).borrowedQuantumLayout.wire
      ((ctx.addOwnedLayout key layout fresh disjoint).borrowedPositionEquiv
        (borrowedPosition ctx key layout fresh disjoint index))).identity =
    (ctx.borrowedQuantumLayout.wire (ctx.borrowedPositionEquiv index)).identity
  exact congrArg QuantumWire.identity
    (((ctx.addOwnedLayout key layout fresh disjoint).borrowedPositionEquiv_wire
      (borrowedPosition ctx key layout fresh disjoint index)).trans
      ((fullPositionEquiv_old_wire ctx key layout fresh disjoint index.val).trans
        (ctx.borrowedPositionEquiv_wire index).symm))

/-- A fixed common borrowed label gives the same finite value at each old borrowed wire. -/
theorem borrowedBasis_value (basis : ctx.borrowedQuantumLayout.Basis)
    (index : QuantumLayout.SelectedPosition ctx.borrowedSelection) :
    ((ctx.addOwnedLayout key layout fresh disjoint).borrowedBasisEquiv.symm basis
      (borrowedPosition ctx key layout fresh disjoint index)).val =
        (ctx.borrowedBasisEquiv.symm basis index).val := by
  have afterValue := (ctx.addOwnedLayout key layout fresh disjoint).borrowedBasisEquiv_value
    ((ctx.addOwnedLayout key layout fresh disjoint).borrowedBasisEquiv.symm basis)
    (borrowedPosition ctx key layout fresh disjoint index)
  have beforeValue := ctx.borrowedBasisEquiv_value (ctx.borrowedBasisEquiv.symm basis) index
  rw [Equiv.apply_symm_apply, borrowedPosition_order] at afterValue
  rw [Equiv.apply_symm_apply] at beforeValue
  exact afterValue.symm.trans beforeValue

private theorem prepared_new_value (newBasis : layout.Basis) (oldBasis : ctx.quantumLayout.Basis)
    (index : Fin count) :
    (preparedLocalBasisEquiv ctx key layout fresh disjoint (newBasis, oldBasis)
      (fullPositionEquiv ctx key layout fresh disjoint (.inl index))).val =
        (newBasis index).val :=
  (ctx.addOwnedLayout_basis_value_preserved key layout fresh disjoint _
    (Fin.castAdd ctx.systemCount index)).trans
      (QuantumLayout.appendJoinBasis_left_value _ _ _ newBasis oldBasis index)

private theorem prepared_old_value (newBasis : layout.Basis) (oldBasis : ctx.quantumLayout.Basis)
    (index : Fin ctx.systemCount) :
    (preparedLocalBasisEquiv ctx key layout fresh disjoint (newBasis, oldBasis)
      (fullPositionEquiv ctx key layout fresh disjoint (.inr index))).val =
        (oldBasis index).val :=
  (ctx.addOwnedLayout_basis_value_preserved key layout fresh disjoint _
    (Fin.natAdd count index)).trans
      (QuantumLayout.appendJoinBasis_right_value _ _ _ newBasis oldBasis index)

/-- Selection reassembly and preparation use precisely the same complete physical basis. -/
theorem join_prepared (borrowed : ctx.borrowedQuantumLayout.Basis)
    (newBasis : layout.Basis)
    (oldComplement : ctx.quantumLayout.ComplementBasis ctx.borrowedSelection) :
    (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout.joinSelectedBasis
      (ctx.addOwnedLayout key layout fresh disjoint).borrowedSelection
      ((ctx.addOwnedLayout key layout fresh disjoint).borrowedBasisEquiv.symm borrowed)
      (complementBasisEquiv ctx key layout fresh disjoint (newBasis, oldComplement)) =
        preparedLocalBasisEquiv ctx key layout fresh disjoint
          (newBasis, ctx.quantumLayout.joinSelectedBasis ctx.borrowedSelection
            (ctx.borrowedBasisEquiv.symm borrowed) oldComplement) := by
  funext position
  obtain ⟨original, rfl⟩ :=
    (fullPositionEquiv ctx key layout fresh disjoint).surjective position
  apply Fin.ext
  cases original with
  | inl index =>
    calc
      _ = (complementBasisEquiv ctx key layout fresh disjoint (newBasis, oldComplement)
          (complementPositionEquiv ctx key layout fresh disjoint (.inl index))).val :=
        congrArg Fin.val
          (QuantumLayout.joinSelectedBasis_complement_value
            (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout _ _ _
              (complementPositionEquiv ctx key layout fresh disjoint (.inl index)))
      _ = (newBasis index).val :=
        complementBasisEquiv_new_value ctx key layout fresh disjoint newBasis oldComplement index
      _ = _ := (prepared_new_value ctx key layout fresh disjoint newBasis _ index).symm
  | inr index =>
    by_cases selected : index ∈ ctx.borrowedSelection
    · calc
        _ = ((ctx.addOwnedLayout key layout fresh disjoint).borrowedBasisEquiv.symm borrowed
            (borrowedPosition ctx key layout fresh disjoint ⟨index, selected⟩)).val :=
          congrArg Fin.val
            (QuantumLayout.joinSelectedBasis_selected_value
              (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout _ _ _
                (borrowedPosition ctx key layout fresh disjoint ⟨index, selected⟩))
        _ = (ctx.borrowedBasisEquiv.symm borrowed ⟨index, selected⟩).val :=
          borrowedBasis_value ctx key layout fresh disjoint borrowed ⟨index, selected⟩
        _ = (ctx.quantumLayout.joinSelectedBasis ctx.borrowedSelection
            (ctx.borrowedBasisEquiv.symm borrowed) oldComplement index).val :=
          (congrArg Fin.val (ctx.quantumLayout.joinSelectedBasis_selected_value _ _ _
            ⟨index, selected⟩)).symm
        _ = _ := (prepared_old_value ctx key layout fresh disjoint newBasis _ index).symm
    · let oldIndex : QuantumLayout.SelectedPosition ctx.borrowedSelectionᶜ :=
        ⟨index, Finset.mem_compl.mpr selected⟩
      calc
        _ = (complementBasisEquiv ctx key layout fresh disjoint (newBasis, oldComplement)
            (complementPositionEquiv ctx key layout fresh disjoint (.inr oldIndex))).val :=
          congrArg Fin.val
            (QuantumLayout.joinSelectedBasis_complement_value
              (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout _ _ _
                (complementPositionEquiv ctx key layout fresh disjoint (.inr oldIndex)))
        _ = (oldComplement oldIndex).val :=
          complementBasisEquiv_old_value ctx key layout fresh disjoint
            newBasis oldComplement oldIndex
        _ = (ctx.quantumLayout.joinSelectedBasis ctx.borrowedSelection
            (ctx.borrowedBasisEquiv.symm borrowed) oldComplement index).val :=
          (congrArg Fin.val (ctx.quantumLayout.joinSelectedBasis_complement_value _ _ _
            oldIndex)).symm
        _ = _ := (prepared_old_value ctx key layout fresh disjoint newBasis _ index).symm

end

end QuantumAlg.Execution.PreparationBorrowed
