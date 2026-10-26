/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.OwnedLayoutView
import all QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Borrowed interfaces retain their physical and classical coordinates

An owned split changes neither borrowed entries nor any actual storage read.
These laws compare the complete ordered interfaces, keeping classical labels
and quantum-reference correlations together [dW19, qcnotes.tex:5381].
-/

namespace QuantumAlg.OwnedLayoutView

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {original viewed : RuntimeCtx .quantum} (view : OwnedLayoutView original viewed)

include view in
/-- Owned slices contribute no borrowed physical wires. -/
lemma borrowedQuantumWires_eq : original.borrowedQuantumWires = viewed.borrowedQuantumWires := by
  have slices : (view.slices.map OwnedLayoutSlice.entry).flatMap
      RuntimeEntry.borrowedQuantumWires = [] := by
    induction view.slices with
    | nil => rfl
    | cons slice rest ih => exact ih
  simp only [RuntimeCtx.borrowedQuantumWires, view.originalEntries, view.viewedEntries,
    List.flatMap_append, List.flatMap_cons, RuntimeEntry.borrowedQuantumWires, List.nil_append]
  rw [slices, List.append_nil]

include view in
/-- Every borrowed classical cell keeps its key, shape and original order. -/
lemma borrowedClassicalCells_eq :
    original.borrowedClassicalCells = viewed.borrowedClassicalCells := by
  have slices : (view.slices.map OwnedLayoutSlice.entry).flatMap
      RuntimeEntry.borrowedClassicalCells = [] := by
    induction view.slices with
    | nil => rfl
    | cons slice rest ih => exact ih
  simp only [RuntimeCtx.borrowedClassicalCells, view.originalEntries, view.viewedEntries,
    List.flatMap_append, List.flatMap_cons, RuntimeEntry.borrowedClassicalCells,
    List.nil_append]
  rw [slices, List.append_nil]

include view in
/-- Borrowed values retain exactly their original structural type. -/
lemma borrowedShape_eq : original.borrowedClassicalShape = viewed.borrowedClassicalShape :=
  RuntimeCtx.borrowedClassicalShape_eq view.borrowedClassicalCells_eq

include view in
/-- Borrowed quantum systems keep the same ordered physical register. -/
lemma borrowedRegister_eq :
    original.borrowedQuantumLayout.register = viewed.borrowedQuantumLayout.register :=
  RuntimeCtx.borrowedRegister_eq view.borrowedQuantumWires_eq

private def borrowedValues (values : ∀ (_key : StorageKey) (shape : CShape), shape.Value) :
    (cells : List (StorageKey × CShape)) → (borrowedCellShape cells).Value
  | [] => .unit
  | cell :: tail => .product (values cell.1 cell.2) (borrowedValues values tail)

private lemma borrowedValues_heq
    (values : ∀ (_key : StorageKey) (shape : CShape), shape.Value)
    {first second : List (StorageKey × CShape)} (same : first = second) :
    HEq (borrowedValues values first) (borrowedValues values second) := by
  cases same
  rfl

private def totalCell
    (values : ∀ (_key : StorageKey) (_role : StorageRole) (shape : CShape), shape.Value) :
    (entry : RuntimeEntry .quantum) → CellValue entry
  | .storage key role shape => values key role shape
  | .borrowedLayout _ _ | .suppliedLayout _ _ | .ownedLayout _ _ | .ownedCopies _ _ => ()

private lemma initializedCell_eq (entries : List (RuntimeEntry .quantum))
    (values : ∀ (_key : StorageKey) (_role : StorageRole) (shape : CShape), shape.Value) :
    Store.initializedCell (entries := entries) (fun key role shape _ => values key role shape) =
      (fun entry _ => totalCell values entry) := by
  funext entry present
  cases entry <;> rfl

private lemma readBorrowedCells_ofValues (entries : List (RuntimeEntry .quantum))
    (values : ∀ (_key : StorageKey) (_role : StorageRole) (shape : CShape), shape.Value) :
    readBorrowedCells entries (Cells.ofValues entries (fun entry _ => totalCell values entry)) =
      borrowedValues (fun key shape => values key .borrowedInput shape)
        (entries.flatMap RuntimeEntry.borrowedClassicalCells) := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
      cases entry with
      | storage key role shape =>
          cases role <;>
            dsimp only [readBorrowedCells, Cells.ofValues, totalCell,
              prependBorrowedCell, RuntimeEntry.borrowedClassicalCells,
              List.flatMap_cons, List.cons_append, List.nil_append, borrowedValues]
          · exact congrArg (CShape.Value.product (values key _ shape)) ih
          all_goals exact ih
      | borrowedLayout | suppliedLayout | ownedLayout | ownedCopies =>
          dsimp only [readBorrowedCells, Cells.ofValues, totalCell,
            prependBorrowedCell, RuntimeEntry.borrowedClassicalCells,
            List.flatMap_cons, List.nil_append]
          exact ih

private lemma store_ofValues_borrowed (ctx : RuntimeCtx .quantum)
    (values : ∀ (_key : StorageKey) (_role : StorageRole) (shape : CShape), shape.Value) :
    (Store.ofValues ctx (fun key role shape _ => values key role shape)).readBorrowedClassical =
      borrowedValues (fun key shape => values key .borrowedInput shape)
        ctx.borrowedClassicalCells := by
  rw [Store.readBorrowedClassical, Store.ofValues, initializedCell_eq]
  exact readBorrowedCells_ofValues _ _

private def totalValues (state : Store original) (key : StorageKey) (role : StorageRole)
    (shape : CShape) : shape.Value :=
  if present : RuntimeEntry.storage key role shape ∈ original.entries then
    state.read (.storage ⟨key, role, ContextPermutation.slotOfMem present⟩)
  else CShape.initialValue shape

private lemma store_eq_ofValues (state : Store original) :
    state = Store.ofValues original (fun key role shape _ => totalValues state key role shape) := by
  apply Store.store_eq_of_storage_reads
  intro shape ref
  rw [Store.read_ofValues]
  simp only [totalValues, dif_pos ref.present]
  congr 2
  exact CStorageRef.storageRef_eq_of_key _ _ rfl

private lemma store_ofValues
    (values : ∀ (_key : StorageKey) (_role : StorageRole) (shape : CShape), shape.Value) :
    view.store (Store.ofValues original (fun key role shape _ => values key role shape)) =
      Store.ofValues viewed (fun key role shape _ => values key role shape) := by
  apply Store.store_eq_of_storage_reads
  intro shape ref
  rw [store, Equiv.coe_fn_mk, storeForward_read, Store.read_ofValues, Store.read_ofValues]
  rfl

/-- Grouping markers cannot change any part of the ordered borrowed classical readout. -/
lemma store_readBorrowedClassical_heq (state : Store original) :
    HEq (view.store state).readBorrowedClassical state.readBorrowedClassical := by
  rw [store_eq_ofValues state, view.store_ofValues]
  rw [store_ofValues_borrowed, store_ofValues_borrowed]
  exact borrowedValues_heq _ view.borrowedClassicalCells_eq.symm

/-- Put the scoped readout on its identical original shape. -/
lemma store_readBorrowedClassical (state : Store original) :
    Equiv.cast (congrArg CShape.Value view.borrowedShape_eq.symm)
      (view.store state).readBorrowedClassical = state.readBorrowedClassical := by
  have cast_eq {α β : Type} (same : α = β) (first : α) (second : β)
      (equal : HEq first second) : Equiv.cast same first = second := by
    cases same
    exact eq_of_heq equal
  exact cast_eq _ _ _ (view.store_readBorrowedClassical_heq state)

/-- The observer's complete data consists of its two physical wire lists. -/
private structure BorrowedWireData where
  wires : List QuantumWire
  borrowed : List QuantumWire
  distinct : (wires.map QuantumWire.identity).Nodup
  borrowedDistinct : (borrowed.map QuantumWire.identity).Nodup
  live : ∀ wire ∈ borrowed, wire ∈ wires

private def BorrowedWireData.ofContext (ctx : RuntimeCtx .quantum) : BorrowedWireData :=
  ⟨ctx.quantumWires, ctx.borrowedQuantumWires, ctx.identitiesNodup,
    ctx.borrowedIdentitiesNodup, fun _ member => ctx.borrowedQuantumWires_sublist.subset member⟩

private lemma BorrowedWireData.eq_of_lists {first second : BorrowedWireData}
    (wires : first.wires = second.wires) (borrowed : first.borrowed = second.borrowed) :
    first = second := by
  cases first
  cases second
  cases wires
  cases borrowed
  rfl

private def BorrowedWireData.layout (data : BorrowedWireData) :=
  QuantumLayout.ofWires data.wires data.distinct

private def BorrowedWireData.borrowedLayout (data : BorrowedWireData) :=
  QuantumLayout.ofWires data.borrowed data.borrowedDistinct

private def BorrowedWireData.selection (data : BorrowedWireData) : Finset (Fin data.wires.length) :=
  Finset.univ.filter fun index => data.layout.wire index ∈ data.borrowed

private lemma BorrowedWireData.mem_selection (data : BorrowedWireData)
    (index : Fin data.wires.length) :
    index ∈ data.selection ↔ data.layout.wire index ∈ data.borrowed := by
  simp only [selection, Finset.mem_filter, Finset.mem_univ, true_and]

private def BorrowedWireData.selectedWireEquiv (data : BorrowedWireData) :
    QuantumLayout.SelectedPosition data.selection ≃
      {wire : QuantumWire // wire ∈ data.borrowed} :=
  Equiv.ofBijective
    (fun index => ⟨data.layout.wire index.val,
      (data.mem_selection index.val).mp index.property⟩) ⟨by
      intro left right same
      apply Subtype.ext
      exact data.layout.identityInjective (congrArg (fun wire => wire.val.identity) same), by
      intro wire
      have live : wire.val ∈ data.layout.wires := by
        change wire.val ∈ (QuantumLayout.ofWires data.wires data.distinct).wires
        rw [QuantumLayout.wires_ofWires]
        exact data.live _ wire.property
      obtain ⟨index, same⟩ := List.mem_ofFn.mp live
      refine ⟨⟨index, (data.mem_selection index).mpr ?_⟩, Subtype.ext same⟩
      rw [same]
      exact wire.property⟩

private def BorrowedWireData.positionEquiv (data : BorrowedWireData) :
    QuantumLayout.SelectedPosition data.selection ≃ Fin data.borrowed.length :=
  data.selectedWireEquiv.trans
    (RuntimeCtx.wireListPositionEquiv data.borrowed
      (List.Nodup.of_map QuantumWire.identity data.borrowedDistinct)).symm

private lemma BorrowedWireData.positionEquiv_wire (data : BorrowedWireData)
    (index : QuantumLayout.SelectedPosition data.selection) :
    data.borrowedLayout.wire (data.positionEquiv index) = data.layout.wire index.val :=
  congrArg Subtype.val (Equiv.apply_symm_apply
    (RuntimeCtx.wireListPositionEquiv data.borrowed
      (List.Nodup.of_map QuantumWire.identity data.borrowedDistinct))
    (data.selectedWireEquiv index))

private def BorrowedWireData.basisEquiv (data : BorrowedWireData) :
    data.layout.SelectedBasis data.selection ≃ data.borrowedLayout.Basis :=
  Equiv.piCongr data.positionEquiv fun index =>
    finCongr (congrArg (fun wire : QuantumWire => (wire.dimension : Nat))
      (data.positionEquiv_wire index).symm)

private def BorrowedWireData.observe (data : BorrowedWireData) (Reference : Register)
    (state : DensityOperator (data.layout.register.prod Reference)) :
    DensityOperator (data.borrowedLayout.register.prod Reference) :=
  (DensityOperator.observeSelectionWithReference data.layout data.selection Reference state).reindex
    (data.basisEquiv.prodCongr (Equiv.refl Reference.Index))

private lemma BorrowedWireData.observe_ofContext (ctx : RuntimeCtx .quantum)
    (Reference : Register) :
    HEq (ctx.observeBorrowedWithReference Reference) ((ofContext ctx).observe Reference) := by
  rfl

include view in
private lemma quantumObservation_heq (Reference : Register) :
    HEq (original.observeBorrowedWithReference Reference)
      (viewed.observeBorrowedWithReference Reference) := by
  have same : BorrowedWireData.ofContext original = BorrowedWireData.ofContext viewed :=
    BorrowedWireData.eq_of_lists view.quantumWires_eq view.borrowedQuantumWires_eq
  have observed : HEq ((BorrowedWireData.ofContext original).observe Reference)
      ((BorrowedWireData.ofContext viewed).observe Reference) := by
    rw [same]
  exact (BorrowedWireData.observe_ofContext original Reference).trans
    (observed.trans (BorrowedWireData.observe_ofContext viewed Reference).symm)


private lemma equalInterfaceObservation {fullFirst fullSecond keptFirst keptSecond : Register}
    (fullEq : fullFirst = fullSecond) (keptEq : keptFirst = keptSecond) (Reference : Register)
    (first : DensityOperator (fullFirst.prod Reference) →
      DensityOperator (keptFirst.prod Reference))
    (second : DensityOperator (fullSecond.prod Reference) →
      DensityOperator (keptSecond.prod Reference)) (same : HEq first second)
    (state : DensityOperator (fullFirst.prod Reference)) :
    (second (state.reindex (S := fullSecond.prod Reference)
      ((Equiv.cast (congrArg Register.Index fullEq)).prodCongr
        (Equiv.refl Reference.Index)))).reindex (S := keptFirst.prod Reference)
        ((Equiv.cast (congrArg Register.Index keptEq.symm)).prodCongr
          (Equiv.refl Reference.Index)) = first state := by
  cases fullEq
  cases keptEq
  have functions : first = second := eq_of_heq same
  rw [← functions]
  change (first (state.reindex (Equiv.refl _))).reindex (Equiv.refl _) = first state
  rw [DensityOperator.reindex_refl, DensityOperator.reindex_refl]

private lemma split_borrowedClassical_block {Reference : Register} {H : Type} [Fintype H]
    (state : State original Reference H) (value : viewed.borrowedClassicalShape.Value) :
    (((view.split state).mapClassical fun label => label.1.readBorrowedClassical).block value) =
      (((state.mapClassical fun label => label.1.readBorrowedClassical).block
        (Equiv.cast (congrArg CShape.Value view.borrowedShape_eq.symm) value)).reindex
          (view.referenceBasis Reference)) := by
  let back := Equiv.cast (congrArg CShape.Value view.borrowedShape_eq.symm)
  have labels : (fun label : Store viewed × H => label.1.readBorrowedClassical) ∘
      view.record H = back.symm ∘
        (fun label : Store original × H => label.1.readBorrowedClassical) := by
    funext label
    apply back.injective
    change back (view.store label.1).readBorrowedClassical =
      back (back.symm label.1.readBorrowedClassical)
    rw [Equiv.apply_symm_apply]
    exact view.store_readBorrowedClassical label.1
  rw [split, ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.executionState_mapClassical_comp, labels,
    ← ExecutionState.executionState_mapClassical_comp]
  change (((state.mapClassical fun label => label.1.readBorrowedClassical).mapClassical
    back.symm).block value).reindex (view.referenceBasis Reference) = _
  rw [ExecutionState.coordinate_mapClassical_block]
  rfl

/-- The complete joint borrowed classical-quantum-reference observation is unchanged. -/
lemma observeBorrowed_split {Reference : Register} {H : Type} [Fintype H]
    (state : State original Reference H) :
    transportBorrowed Reference view.borrowedShape_eq.symm view.borrowedRegister_eq.symm
      (observeBorrowed Reference (view.split state)) = observeBorrowed Reference state := by
  rw [transportBorrowed_eq_reindex]
  apply ExecutionState.ext
  intro value
  rw [ExecutionState.coordinate_mapClassical_block]
  change (viewed.observeBorrowedWithReference Reference
    (((view.split state).mapClassical fun label => label.1.readBorrowedClassical).block
      ((Equiv.cast (congrArg CShape.Value view.borrowedShape_eq.symm)).symm value))).reindex
        (S := original.borrowedQuantumLayout.register.prod Reference)
        ((Equiv.cast (congrArg Register.Index view.borrowedRegister_eq.symm)).prodCongr
          (Equiv.refl Reference.Index)) = _
  rw [view.split_borrowedClassical_block, Equiv.apply_symm_apply]
  exact equalInterfaceObservation view.register_eq view.borrowedRegister_eq Reference
    (original.observeBorrowedWithReference Reference)
    (viewed.observeBorrowedWithReference Reference) (view.quantumObservation_heq Reference) _

/-- Restoring the original grouping transports exactly the same complete borrowed state. -/
lemma observeBorrowed_join {Reference : Register} {H : Type} [Fintype H]
    (state : State viewed Reference H) :
    observeBorrowed Reference (view.join state) =
      transportBorrowed Reference view.borrowedShape_eq.symm view.borrowedRegister_eq.symm
        (observeBorrowed Reference state) := by
  have same := view.observeBorrowed_split (view.join state)
  rw [view.split_join] at same
  exact same.symm

end

end QuantumAlg.OwnedLayoutView
