/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Ordered views of one owned physical layout

A view changes the grouping of one owned entry into ordered owned slices.
The complete ordered physical wire records are identical. All other entries,
including classical cells and their accounting roles, remain literally present.
The descriptor supplies no operation, state preparation or Hilbert-space map.
-/

namespace QuantumAlg

/-- One named, ordered slice of an existing owned physical layout. -/
public structure OwnedLayoutSlice where
  /-- Scoped storage identity of the slice. -/
  key : StorageKey
  /-- Number of physical systems in the slice. -/
  count : Nat
  /-- The existing physical systems, in their original order. -/
  layout : QuantumLayout count

namespace OwnedLayoutSlice

/-- The slice remains algorithm-owned auxiliary storage. -/
public def entry (slice : OwnedLayoutSlice) : RuntimeEntry .quantum :=
  .ownedLayout slice.key slice.layout

end OwnedLayoutSlice

/-- A scoped regrouping of exactly one owned layout, with all physical wires fixed. -/
public structure OwnedLayoutView (original viewed : RuntimeCtx .quantum) where
  /-- Unchanged entries preceding the split entry. -/
  before : List (RuntimeEntry .quantum)
  /-- Unchanged entries following the split entry. -/
  after : List (RuntimeEntry .quantum)
  /-- Original storage identity. -/
  key : StorageKey
  /-- Original number of physical systems. -/
  count : Nat
  /-- Original complete owned layout. -/
  layout : QuantumLayout count
  /-- Ordered owned slices visible only inside the scope. -/
  slices : List OwnedLayoutSlice
  /-- The original context contains exactly the selected owned entry here. -/
  originalEntries : original.entries = before ++ .ownedLayout key layout :: after
  /-- Only this entry is replaced inside the view. -/
  viewedEntries : viewed.entries = before ++ slices.map OwnedLayoutSlice.entry ++ after
  /-- Every physical wire record is retained in its exact original order. -/
  sliceWires : (slices.flatMap fun slice => slice.layout.wires) = layout.wires

namespace OwnedLayoutView

/-- Build the scoped context directly from the selected entry and actual ordered slices.
Only storage-key uniqueness is new: physical uniqueness follows from the original wires. -/
public def scopedContext (original : RuntimeCtx .quantum)
    (before after : List (RuntimeEntry .quantum)) (key : StorageKey) {count : Nat}
    (layout : QuantumLayout count)
    (originalEntries : original.entries = before ++ .ownedLayout key layout :: after)
    (slices : List OwnedLayoutSlice)
    (sliceWires : (slices.flatMap fun slice => slice.layout.wires) = layout.wires)
    (keysNodup : ((before ++ slices.map OwnedLayoutSlice.entry ++ after).map
      RuntimeEntry.key).Nodup) : RuntimeCtx .quantum :=
  RuntimeCtx.ofEntries (before ++ slices.map OwnedLayoutSlice.entry ++ after) keysNodup (by
    have wires : (before ++ slices.map OwnedLayoutSlice.entry ++ after).flatMap
        RuntimeEntry.quantumWires = original.quantumWires := by
      simp only [RuntimeCtx.quantumWires, originalEntries, List.flatMap_append,
        List.flatMap_cons, List.flatMap_map, OwnedLayoutSlice.entry, RuntimeEntry.quantumWires]
      rw [sliceWires]
      simp only [List.append_assoc]
    rw [wires]
    exact original.identitiesNodup)

/-- The constructed context carries its complete strict owned-split certificate. -/
public def ofSlices (original : RuntimeCtx .quantum)
    (before after : List (RuntimeEntry .quantum)) (key : StorageKey) {count : Nat}
    (layout : QuantumLayout count)
    (originalEntries : original.entries = before ++ .ownedLayout key layout :: after)
    (slices : List OwnedLayoutSlice)
    (sliceWires : (slices.flatMap fun slice => slice.layout.wires) = layout.wires)
    (keysNodup : ((before ++ slices.map OwnedLayoutSlice.entry ++ after).map
      RuntimeEntry.key).Nodup) :
    OwnedLayoutView original
      (scopedContext original before after key layout originalEntries
        slices sliceWires keysNodup) :=
  ⟨before, after, key, count, layout, slices, originalEntries, rfl, sliceWires⟩

variable {original viewed : RuntimeCtx .quantum} (view : OwnedLayoutView original viewed)

include view

/-- Regrouping preserves the complete ordered physical wire sequence. -/
public lemma quantumWires_eq : original.quantumWires = viewed.quantumWires := by
  simp only [RuntimeCtx.quantumWires, view.originalEntries, view.viewedEntries,
    List.flatMap_append, List.flatMap_cons, List.flatMap_map,
    OwnedLayoutSlice.entry, RuntimeEntry.quantumWires]
  rw [view.sliceWires]
  simp only [List.append_assoc]

/-- Each classical cell retains its original key, role, shape and presence. -/
public lemma storage_mem_iff (key : StorageKey) (role : StorageRole) (shape : CShape) :
    RuntimeEntry.storage key role shape ∈ original.entries ↔
      RuntimeEntry.storage key role shape ∈ viewed.entries := by
  have absent : RuntimeEntry.storage key role shape ∉
      view.slices.map OwnedLayoutSlice.entry := by
    simp only [List.mem_map, OwnedLayoutSlice.entry]
    rintro ⟨slice, _, impossible⟩
    cases impossible
  simp [view.originalEntries, view.viewedEntries, absent]

private def wireListRegister (wires : List QuantumWire) : Register where
  Index := (index : Fin wires.length) → Fin (wires.get index).dimension
  fintype := inferInstance
  decEq := inferInstance

/-- The complete quantum register depends only on these exact ordered physical wires. -/
public lemma register_eq : original.register = viewed.register :=
  congrArg wireListRegister view.quantumWires_eq

private lemma slices_residentSpace :
    (view.slices.map OwnedLayoutSlice.entry).foldr
      (fun entry total => entry.residentSpace + total) 0 =
        SpacePool.ofQuantumLayout view.layout := by
  have wires : (view.slices.map OwnedLayoutSlice.entry).flatMap RuntimeEntry.quantumWires =
      view.layout.wires := by
    simpa only [List.flatMap_map, OwnedLayoutSlice.entry, RuntimeEntry.quantumWires] using
      view.sliceWires
  ext axis
  cases axis with
  | classicalBits =>
      have zero (slices : List OwnedLayoutSlice) :
          ((slices.map OwnedLayoutSlice.entry).foldr
            (fun (entry : RuntimeEntry .quantum) (total : SpacePool .quantum) =>
              entry.residentSpace + total) 0) .classicalBits = 0 := by
        induction slices with
        | nil => rfl
        | cons slice slices ih =>
            simpa only [List.map_cons, List.foldr_cons, OwnedLayoutSlice.entry,
              RuntimeEntry.residentSpace, Pi.add_apply, SpacePool.ofQuantumLayout,
              Nat.zero_add] using ih
      exact zero _
  | quantumSystems dimension =>
      rw [RuntimeCtx.residentSpace_quantumSystems_entries, wires]
      exact (RuntimeEntry.residentSpace_quantumSystems
        (.ownedLayout view.key view.layout) dimension).symm

private lemma slices_auxiliarySpace :
    (view.slices.map OwnedLayoutSlice.entry).foldr
      (fun entry total => entry.auxiliarySpace + total) 0 =
        SpacePool.ofQuantumLayout view.layout := by
  simpa only [List.foldr_map, Function.comp_def, OwnedLayoutSlice.entry,
    RuntimeEntry.residentSpace, RuntimeEntry.auxiliarySpace] using view.slices_residentSpace

/-- Splitting an owned entry preserves every resident classical and quantum space coordinate. -/
public lemma residentSpace_eq : original.residentSpace = viewed.residentSpace := by
  simp only [RuntimeCtx.residentSpace, view.originalEntries, view.viewedEntries,
    RuntimeCtx.foldSpace_append, List.foldr_cons]
  rw [view.slices_residentSpace]
  ext axis
  exact (Nat.add_assoc _ _ _).symm

/-- Every slice remains owned; all other accounting roles are unchanged. -/
public lemma auxiliarySpace_eq : original.auxiliarySpace = viewed.auxiliarySpace := by
  simp only [RuntimeCtx.auxiliarySpace, view.originalEntries, view.viewedEntries,
    RuntimeCtx.foldSpace_append, List.foldr_cons]
  rw [view.slices_auxiliarySpace]
  ext axis
  exact (Nat.add_assoc _ _ _).symm

end OwnedLayoutView

end QuantumAlg
