/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Base.Accounting.Context
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fin.SuccPred
import Mathlib.Logic.Equiv.Basic

/-!
# Actual borrowed systems and their joint reference observation

Borrowed systems are the wires of borrowed layout entries, in context entry
order and then layout order. Owned layouts and banks are excluded. The common
borrowed register is derived from those complete wire records, including their
physical identities and dimensions.

Circuit construction preserves this borrowed layout. That fact alone proves
no restoration of its state: restoration must compare the input and output
density observations jointly with the external reference. These observations
retain mixed-state correlations [dW19, qcnotes.tex:5381] and do not change
storage ownership, state promises, or accounting.
-/

namespace QuantumAlg

namespace RuntimeEntry

/-- Only a borrowed layout contributes borrowed quantum wires. -/
@[implicit_reducible]
def borrowedQuantumWires {kind : ProblemKind} : RuntimeEntry kind → List QuantumWire
  | .storage _ _ _ => []
  | .borrowedLayout _ layout => layout.wires
  | .ownedLayout _ _ => []
  | .ownedCopies _ _ => []

/-- Borrowed wires retain their actual positions within the entry's full wire list. -/
theorem borrowedQuantumWires_sublist {kind : ProblemKind} (entry : RuntimeEntry kind) :
    entry.borrowedQuantumWires.Sublist entry.quantumWires := by
  cases entry with
  | storage => exact List.Sublist.refl _
  | borrowedLayout => exact List.Sublist.refl _
  | ownedLayout => exact List.nil_sublist _
  | ownedCopies => exact List.nil_sublist _

end RuntimeEntry

namespace RuntimeCtx

variable {kind : ProblemKind}

/-- All borrowed wire records in their original entry and layout order. -/
@[implicit_reducible]
def borrowedQuantumWires (ctx : RuntimeCtx kind) : List QuantumWire :=
  ctx.entries.flatMap RuntimeEntry.borrowedQuantumWires

/-- The borrowed list is an order-preserving part of the complete physical frame. -/
theorem borrowedQuantumWires_sublist (ctx : RuntimeCtx kind) :
    ctx.borrowedQuantumWires.Sublist ctx.quantumWires :=
  List.Sublist.flatMap_right ctx.entries fun entry _ => entry.borrowedQuantumWires_sublist

/-- Borrowed wires inherit the context's global uniqueness of physical identities. -/
theorem borrowedIdentitiesNodup (ctx : RuntimeCtx kind) :
    (ctx.borrowedQuantumWires.map QuantumWire.identity).Nodup :=
  (ctx.borrowedQuantumWires_sublist.map QuantumWire.identity).nodup ctx.identitiesNodup

/-- In particular, the complete borrowed wire records do not repeat. -/
theorem borrowedQuantumWires_nodup (ctx : RuntimeCtx kind) : ctx.borrowedQuantumWires.Nodup :=
  List.Nodup.of_map QuantumWire.identity ctx.borrowedIdentitiesNodup

/-- The common borrowed layout uses the original ordered wire records. -/
@[implicit_reducible]
def borrowedQuantumLayout (ctx : RuntimeCtx kind) :
    QuantumLayout ctx.borrowedQuantumWires.length :=
  QuantumLayout.ofWires ctx.borrowedQuantumWires ctx.borrowedIdentitiesNodup

@[simp] theorem borrowedQuantumLayout_wires (ctx : RuntimeCtx kind) :
    ctx.borrowedQuantumLayout.wires = ctx.borrowedQuantumWires :=
  QuantumLayout.wires_ofWires ctx.borrowedQuantumWires ctx.borrowedIdentitiesNodup

@[simp] theorem borrowedQuantumWires_empty :
    (RuntimeCtx.empty : RuntimeCtx kind).borrowedQuantumWires = [] := rfl

/-- Allocating classical input does not add or remove borrowed quantum systems. -/
@[simp] theorem borrowedQuantumWires_addBorrowedInput (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (ctx.addBorrowedInput key shape fresh).borrowedQuantumWires = ctx.borrowedQuantumWires := rfl

/-- Classical lexical workspace leaves the ordered borrowed quantum frame unchanged. -/
@[simp] theorem borrowedQuantumWires_addWorkspace (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (ctx.addWorkspace key shape fresh).borrowedQuantumWires = ctx.borrowedQuantumWires := rfl

/-- Retaining classical data leaves every borrowed physical wire unchanged. -/
@[simp] theorem borrowedQuantumWires_addRetained (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (ctx.addRetained key shape fresh).borrowedQuantumWires = ctx.borrowedQuantumWires := rfl

/-- Declaring classical output storage does not alter the borrowed quantum frame. -/
@[simp] theorem borrowedQuantumWires_addFinalOutput (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (ctx.addFinalOutput key shape fresh).borrowedQuantumWires = ctx.borrowedQuantumWires := rfl

/-- New owned systems are excluded from the borrowed frame. -/
@[simp] theorem borrowedQuantumWires_addOwnedLayout (ctx : RuntimeCtx .quantum)
    (key : StorageKey) {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (ctx.addOwnedLayout key layout fresh disjoint).borrowedQuantumWires =
      ctx.borrowedQuantumWires := rfl

/-- Every member of a newly owned bank remains outside the borrowed frame. -/
@[simp] theorem borrowedQuantumWires_addOwnedCopies (ctx : RuntimeCtx .quantum)
    (key : StorageKey) {copyCount systemsPerCopy : Nat}
    (bank : OwnedCopyBank copyCount systemsPerCopy) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint bank.identities ctx.physicalIdx) :
    (ctx.addOwnedCopies key bank fresh disjoint).borrowedQuantumWires =
      ctx.borrowedQuantumWires := rfl

/-- Explicitly supplying another borrowed layout extends the caller's borrowed frame. -/
@[simp] theorem borrowedQuantumWires_addBorrowedLayout (ctx : RuntimeCtx .quantum)
    (key : StorageKey) {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (ctx.addBorrowedLayout key layout fresh disjoint).borrowedQuantumWires =
      layout.wires ++ ctx.borrowedQuantumWires := rfl

/-- A disjoint newly owned wire cannot be mistaken for any original borrowed wire. -/
theorem ownedLayout_wire_not_borrowed (ctx : RuntimeCtx .quantum)
    (key : StorageKey) {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (index : Fin systemCount) :
    layout.wire index ∉ (ctx.addOwnedLayout key layout fresh disjoint).borrowedQuantumWires := by
  intro member
  have live : layout.wire index ∈ ctx.quantumWires :=
    ctx.borrowedQuantumWires_sublist.subset member
  exact disjoint (List.mem_ofFn.mpr ⟨index, rfl⟩) (List.mem_map_of_mem live)

/-- Select precisely those global positions whose actual wire is borrowed. -/
def borrowedSelection (ctx : RuntimeCtx kind) : Finset (Fin ctx.systemCount) :=
  Finset.univ.filter fun index => ctx.quantumLayout.wire index ∈ ctx.borrowedQuantumWires

@[simp] theorem mem_borrowedSelection (ctx : RuntimeCtx kind) (index : Fin ctx.systemCount) :
    index ∈ ctx.borrowedSelection ↔ ctx.quantumLayout.wire index ∈ ctx.borrowedQuantumWires := by
  simp only [borrowedSelection, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable section

/-- Match each position to its own wire record in a duplicate-free list. -/
private def wireListPositionEquiv (wires : List QuantumWire) (distinct : wires.Nodup) :
    Fin wires.length ≃ {wire : QuantumWire // wire ∈ wires} :=
  Equiv.ofBijective (fun index => ⟨wires.get index, List.get_mem wires index⟩) ⟨by
    intro left right same
    exact distinct.injective_get (congrArg Subtype.val same), by
    intro wire
    obtain ⟨index, same⟩ := List.mem_iff_get.mp wire.property
    exact ⟨index, Subtype.ext same⟩⟩

/-- Selected global positions match borrowed records by their actual wires. -/
private def selectedBorrowedWireEquiv (ctx : RuntimeCtx kind) :
    QuantumLayout.SelectedPosition ctx.borrowedSelection ≃
      {wire : QuantumWire // wire ∈ ctx.borrowedQuantumWires} :=
  Equiv.ofBijective
    (fun index => ⟨ctx.quantumLayout.wire index.val,
      (ctx.mem_borrowedSelection index.val).mp index.property⟩) ⟨by
      intro left right same
      apply Subtype.ext
      exact ctx.quantumLayout.identityInjective
        (congrArg (fun wire => wire.val.identity) same), by
      intro wire
      have live : wire.val ∈ ctx.quantumLayout.wires := by
        rw [ctx.quantumLayout_wires]
        exact ctx.borrowedQuantumWires_sublist.subset wire.property
      obtain ⟨index, same⟩ := List.mem_ofFn.mp live
      refine ⟨⟨index, (ctx.mem_borrowedSelection index).mpr ?_⟩, Subtype.ext same⟩
      rw [same]
      exact wire.property⟩

/-- The correspondence to the common ordered borrowed frame follows actual wire identity. -/
def borrowedPositionEquiv (ctx : RuntimeCtx kind) :
    QuantumLayout.SelectedPosition ctx.borrowedSelection ≃
      Fin ctx.borrowedQuantumWires.length :=
  (selectedBorrowedWireEquiv ctx).trans
    (wireListPositionEquiv ctx.borrowedQuantumWires ctx.borrowedQuantumWires_nodup).symm

/-- Corresponding positions carry the very same wire, including identity and dimension. -/
theorem borrowedPositionEquiv_wire (ctx : RuntimeCtx kind)
    (index : QuantumLayout.SelectedPosition ctx.borrowedSelection) :
    ctx.borrowedQuantumLayout.wire (ctx.borrowedPositionEquiv index) =
      ctx.quantumLayout.wire index.val :=
  congrArg Subtype.val
    (Equiv.apply_symm_apply
      (wireListPositionEquiv ctx.borrowedQuantumWires ctx.borrowedQuantumWires_nodup)
      (selectedBorrowedWireEquiv ctx index))

/-- Transport finite basis values only across their proved equal physical dimensions. -/
def borrowedBasisEquiv (ctx : RuntimeCtx kind) :
    ctx.quantumLayout.SelectedBasis ctx.borrowedSelection ≃ ctx.borrowedQuantumLayout.Basis :=
  Equiv.piCongr ctx.borrowedPositionEquiv fun index =>
    finCongr (congrArg (fun wire : QuantumWire => (wire.dimension : Nat))
      (ctx.borrowedPositionEquiv_wire index).symm)

/-- The common borrowed basis retains each actual wire's finite value unchanged. -/
theorem borrowedBasisEquiv_value (ctx : RuntimeCtx kind)
    (basis : ctx.quantumLayout.SelectedBasis ctx.borrowedSelection)
    (index : QuantumLayout.SelectedPosition ctx.borrowedSelection) :
    (ctx.borrowedBasisEquiv basis (ctx.borrowedPositionEquiv index)).val = (basis index).val := by
  simp only [borrowedBasisEquiv, Equiv.piCongr_apply_apply, finCongr_apply_coe]

/-- Observe all borrowed systems jointly with the reference on their common ordered register. -/
def observeBorrowedWithReference (ctx : RuntimeCtx kind) (Reference : Register)
    (state : DensityOperator (Register.prod ctx.register Reference)) :
    DensityOperator (Register.prod ctx.borrowedQuantumLayout.register Reference) :=
  (DensityOperator.observeSelectionWithReference ctx.quantumLayout ctx.borrowedSelection
    Reference state).reindex
      (S := Register.prod ctx.borrowedQuantumLayout.register Reference)
      (ctx.borrowedBasisEquiv.prodCongr (Equiv.refl Reference.Index))

/-- The common observation sums only complementary wires and keeps all reference coherences. -/
theorem observeBorrowedWithReference_entry (ctx : RuntimeCtx kind) (Reference : Register)
    (state : DensityOperator (Register.prod ctx.register Reference))
    (row column : ctx.borrowedQuantumLayout.Basis) (refRow refColumn : Reference.Index) :
    (ctx.observeBorrowedWithReference Reference state).matrix (row, refRow) (column, refColumn) =
      ∑ complement : ctx.quantumLayout.ComplementBasis ctx.borrowedSelection,
        state.matrix
          (ctx.quantumLayout.joinSelectedBasis ctx.borrowedSelection
            (ctx.borrowedBasisEquiv.symm row) complement, refRow)
          (ctx.quantumLayout.joinSelectedBasis ctx.borrowedSelection
            (ctx.borrowedBasisEquiv.symm column) complement, refColumn) := by
  exact DensityOperator.observeSelectionWithReference_entry ctx.quantumLayout
    ctx.borrowedSelection Reference state (ctx.borrowedBasisEquiv.symm row)
      (ctx.borrowedBasisEquiv.symm column) refRow refColumn

/-- Observing borrowed systems and their reference preserves probability mass. -/
theorem observeBorrowedWithReference_mass (ctx : RuntimeCtx kind) (Reference : Register)
    (state : DensityOperator (Register.prod ctx.register Reference)) :
    (ctx.observeBorrowedWithReference Reference state).mass = state.mass := by
  exact (DensityOperator.reindex_mass
    (R := Register.prod (ctx.quantumLayout.selectedRegister ctx.borrowedSelection) Reference)
    (S := Register.prod ctx.borrowedQuantumLayout.register Reference)
    (DensityOperator.observeSelectionWithReference ctx.quantumLayout ctx.borrowedSelection
      Reference state) (ctx.borrowedBasisEquiv.prodCongr (Equiv.refl Reference.Index))).trans
    (DensityOperator.observeSelectionWithReference_mass ctx.quantumLayout
      ctx.borrowedSelection Reference state)

end

/-- The basis carrier of an ordered wire list does not depend on its identity proof. -/
private def wireListRegister (wires : List QuantumWire) : Register where
  Index := (index : Fin wires.length) → Fin (wires.get index).dimension
  fintype := inferInstance
  decEq := inferInstance

/-- Equal ordered borrowed wire lists determine one common finite register. -/
theorem borrowedRegister_eq {pre post : RuntimeCtx kind}
    (same : pre.borrowedQuantumWires = post.borrowedQuantumWires) :
    pre.borrowedQuantumLayout.register = post.borrowedQuantumLayout.register :=
  congrArg wireListRegister same

end RuntimeCtx

namespace Circuit

/-- Circuit allocation and classical lexical release preserve the full borrowed wire list.
This is a placement invariant, not a claim that the quantum state has been restored. -/
theorem borrowedQuantumWires_preserved {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) : post.borrowedQuantumWires = pre.borrowedQuantumWires := by
  induction code with
  | id | classical | declaredCall | unitary | measureZ | randomBits | iterate | workspace => rfl
  | retain ctx key shape fresh => exact ctx.borrowedQuantumWires_addRetained key shape fresh
  | prepare ctx key layout fresh disjoint preparation =>
      exact ctx.borrowedQuantumWires_addOwnedLayout key layout fresh disjoint
  | seq first second firstIH secondIH => exact secondIH.trans firstIH
  | branch input body bodyIH => exact bodyIH (CShape.initialValue _)

/-- Before and after a circuit, the common borrowed register uses identical wire records. -/
theorem borrowedRegister_preserved {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) :
    post.borrowedQuantumLayout.register = pre.borrowedQuantumLayout.register :=
  RuntimeCtx.borrowedRegister_eq code.borrowedQuantumWires_preserved

/-- Coordinate transport for comparing borrowed observations across this exact circuit. -/
def borrowedBasisTransport {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) :
    post.borrowedQuantumLayout.register.Index ≃ pre.borrowedQuantumLayout.register.Index :=
  Equiv.cast (congrArg Register.Index code.borrowedRegister_preserved)

end Circuit

end QuantumAlg
