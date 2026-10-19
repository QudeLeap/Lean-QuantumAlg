/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Borrowed
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Physical borrowed and complementary positions after fresh preparation

Fresh owned positions are disjoint from every original borrowed wire. The
complementary positions after preparation are exactly the fresh positions
and the original complement, retaining the physical identities and local
dimensions of both parts. The correspondence uses the actual appended wire
lists and does not depend on a quantum state or a Hilbert-space cardinality.
-/

namespace QuantumAlg.Execution.PreparationBorrowed

noncomputable section

variable {count : Nat} (ctx : RuntimeCtx .quantum) (key : StorageKey)
  (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
  (disjoint : List.Disjoint layout.identities ctx.physicalIdx)

/-- Actual positions of the newly prepared and original physical systems. -/
def fullPositionEquiv : Fin count ⊕ Fin ctx.systemCount ≃
    Fin (ctx.addOwnedLayout key layout fresh disjoint).systemCount :=
  finSumFinEquiv.trans (ctx.addOwnedLayoutPositionEquiv key layout fresh disjoint)

/-- A fresh position keeps its complete wire record. -/
lemma fullPositionEquiv_new_wire (index : Fin count) :
    (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout.wire
      (fullPositionEquiv ctx key layout fresh disjoint (.inl index)) = layout.wire index := by
  rw [fullPositionEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left,
    RuntimeCtx.addOwnedLayout_wire_preserved]
  simp only [QuantumLayout.append, Fin.append_left]

/-- An old position keeps its complete wire record. -/
lemma fullPositionEquiv_old_wire (index : Fin ctx.systemCount) :
    (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout.wire
      (fullPositionEquiv ctx key layout fresh disjoint (.inr index)) =
        ctx.quantumLayout.wire index := by
  rw [fullPositionEquiv, Equiv.trans_apply, finSumFinEquiv_apply_right,
    RuntimeCtx.addOwnedLayout_wire_preserved]
  simp only [QuantumLayout.append, Fin.append_right]

/-- Every newly prepared position lies outside the original borrowed selection. -/
lemma fullPositionEquiv_new_complement (index : Fin count) :
    fullPositionEquiv ctx key layout fresh disjoint (.inl index) ∈
      (ctx.addOwnedLayout key layout fresh disjoint).borrowedSelectionᶜ := by
  rw [Finset.mem_compl, RuntimeCtx.mem_borrowedSelection, fullPositionEquiv_new_wire]
  exact ctx.ownedLayout_wire_not_borrowed key layout fresh disjoint index

/-- Preparation leaves the borrowed status of every original physical position unchanged. -/
lemma fullPositionEquiv_old_borrowed (index : Fin ctx.systemCount) :
    fullPositionEquiv ctx key layout fresh disjoint (.inr index) ∈
      (ctx.addOwnedLayout key layout fresh disjoint).borrowedSelection ↔
        index ∈ ctx.borrowedSelection := by
  rw [RuntimeCtx.mem_borrowedSelection, RuntimeCtx.mem_borrowedSelection,
    fullPositionEquiv_old_wire, RuntimeCtx.borrowedQuantumWires_addOwnedLayout]

private def complementPositionMap :
    Fin count ⊕ QuantumLayout.SelectedPosition ctx.borrowedSelectionᶜ →
      QuantumLayout.SelectedPosition
        (ctx.addOwnedLayout key layout fresh disjoint).borrowedSelectionᶜ
  | .inl index => ⟨fullPositionEquiv ctx key layout fresh disjoint (.inl index),
      fullPositionEquiv_new_complement ctx key layout fresh disjoint index⟩
  | .inr index => ⟨fullPositionEquiv ctx key layout fresh disjoint (.inr index.val), by
      rw [Finset.mem_compl, fullPositionEquiv_old_borrowed]
      exact Finset.mem_compl.mp index.property⟩

private lemma complementPositionMap_injective :
    Function.Injective (complementPositionMap ctx key layout fresh disjoint) := by
  intro left right same
  have positions :
      fullPositionEquiv ctx key layout fresh disjoint (Sum.map id Subtype.val left) =
        fullPositionEquiv ctx key layout fresh disjoint (Sum.map id Subtype.val right) := by
    cases left <;> cases right <;> exact congrArg Subtype.val same
  have original := (fullPositionEquiv ctx key layout fresh disjoint).injective positions
  cases left with
  | inl left =>
    cases right with
    | inl right => exact congrArg Sum.inl (Sum.inl.inj original)
    | inr right => cases original
  | inr left =>
    cases right with
    | inl right => cases original
    | inr right => exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj original))

private lemma complementPositionMap_surjective :
    Function.Surjective (complementPositionMap ctx key layout fresh disjoint) := by
  intro position
  obtain ⟨original, same⟩ :=
    (fullPositionEquiv ctx key layout fresh disjoint).surjective position.val
  cases original with
  | inl index => exact ⟨.inl index, Subtype.ext same⟩
  | inr index =>
    have outside : index ∈ ctx.borrowedSelectionᶜ := by
      rw [Finset.mem_compl, ← fullPositionEquiv_old_borrowed ctx key layout fresh disjoint,
        same]
      exact Finset.mem_compl.mp position.property
    exact ⟨.inr ⟨index, outside⟩, Subtype.ext same⟩

/-- The exact new complement consists of the fresh systems and the original complement. -/
def complementPositionEquiv :
    Fin count ⊕ QuantumLayout.SelectedPosition ctx.borrowedSelectionᶜ ≃
      QuantumLayout.SelectedPosition
        (ctx.addOwnedLayout key layout fresh disjoint).borrowedSelectionᶜ :=
  Equiv.ofBijective (complementPositionMap ctx key layout fresh disjoint)
    ⟨complementPositionMap_injective ctx key layout fresh disjoint,
      complementPositionMap_surjective ctx key layout fresh disjoint⟩

/-- Corresponding complementary positions preserve their exact local dimension. -/
lemma complementPositionEquiv_dimension
    (index : Fin count ⊕ QuantumLayout.SelectedPosition ctx.borrowedSelectionᶜ) :
    ((ctx.addOwnedLayout key layout fresh disjoint).quantumLayout.wire
      (complementPositionEquiv ctx key layout fresh disjoint index).val).dimension =
        Sum.elim (fun position => (layout.wire position).dimension)
          (fun position => (ctx.quantumLayout.wire position.val).dimension) index := by
  cases index with
  | inl index =>
    exact congrArg QuantumWire.dimension
      (fullPositionEquiv_new_wire ctx key layout fresh disjoint index)
  | inr index =>
    exact congrArg QuantumWire.dimension
      (fullPositionEquiv_old_wire ctx key layout fresh disjoint index.val)

end

end QuantumAlg.Execution.PreparationBorrowed
