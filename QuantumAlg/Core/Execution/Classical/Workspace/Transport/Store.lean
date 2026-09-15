/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Write

/-!
# Restricting actual stores along structural workspace transport

Restriction constructs the existing caller-shaped Store from its transported
storage values. This is a mathematical projection of classical cells.
Allocation, output release and quantum state changes belong to Circuit execution.
-/

namespace QuantumAlg.Execution.ClassicalWorkspace.Transport

private theorem entrySlot_nonempty_of_mem {kind : ProblemKind} {entry : RuntimeEntry kind}
    {entries : List (RuntimeEntry kind)} (present : entry ∈ entries) :
    Nonempty (RuntimeEntrySlot entry entries) := by
  induction entries with
  | nil => exact False.elim (List.not_mem_nil present)
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp present with same | present
      · cases same
        exact ⟨.here⟩
      · obtain ⟨slot⟩ := inductionHypothesis present
        exact ⟨.there slot⟩

private noncomputable def storageRefOfMem {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (role : StorageRole) (shape : CShape)
    (present : RuntimeEntry.storage key role shape ∈ ctx.entries) : CStorageRef ctx shape where
  key := key
  role := role
  slot := Classical.choice (entrySlot_nonempty_of_mem present)

/-- Project transported classical values into the existing caller-shaped Store. -/
noncomputable def restrict {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    (transport : Transport outer inner) (store : Store inner) : Store outer :=
  Store.ofValues outer fun key role shape present =>
    store.read (.storage (transport.liftStorage (storageRefOfMem outer key role shape present)))

/-- Restriction agrees with every actual transported structural input read. -/
theorem workspaceTransport_restrict_readsAs {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} (transport : Transport outer inner) (store : Store inner) :
    transport.ReadsAs (transport.restrict store) store := by
  intro shape input
  induction input with
  | storage ref =>
      rw [restrict, Store.read_ofValues]
      have same := CStorageRef.storageRef_eq_of_key
        (storageRefOfMem outer ref.key ref.role _ ref.present) ref rfl
      exact congrArg (fun selected => store.read (.storage (transport.liftStorage selected)))
        same.symm
  | product left right leftIH rightIH => exact congrArg₂ CShape.Value.product leftIH rightIH
  | fixedVector entries entriesIH => exact congrArg CShape.Value.fixedVector (funext entriesIH)
  | first input ih => exact congrArg CShape.Value.first ih
  | second input ih => exact congrArg CShape.Value.second ih
  | vectorGet input index ih => exact congrArg (fun entry => entry.get index) ih
  | bitsGet input index ih => exact congrArg (fun entry => entry.bitGet index) ih
  | wordBitGet input index ih => exact congrArg (fun entry => entry.wordBitGet index) ih

/-- Agreement of actual transported reads is equality with the restricted caller Store. -/
theorem workspaceTransport_readsAs_restrict_iff {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} (transport : Transport outer inner)
    {source : Store outer} {after : Store inner} :
    transport.ReadsAs source after ↔ transport.restrict after = source := by
  constructor
  · intro reads
    apply Store.store_eq_of_storage_reads
    intro shape input
    exact (transport.workspaceTransport_restrict_readsAs after (.storage input)).symm.trans
      (reads (.storage input))
  · rintro rfl
    exact transport.workspaceTransport_restrict_readsAs after

/-- Identity restriction returns the same actual Store. -/
theorem workspaceTransport_restrict_id {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (store : Store ctx) : (id ctx).restrict store = store :=
  (workspaceTransport_readsAs_restrict_iff (id ctx)).mp (workspaceTransport_readsAs_id store)

/-- Restriction composes through the same intermediate classical store values. -/
theorem workspaceTransport_restrict_compose {kind : ProblemKind}
    {outer middle inner : RuntimeCtx kind}
    (first : Transport outer middle) (second : Transport middle inner) (store : Store inner) :
    (first.compose second).restrict store = first.restrict (second.restrict store) := by
  apply (workspaceTransport_readsAs_restrict_iff (first.compose second)).mp
  exact workspaceTransport_readsAs_compose first second
    (first.workspaceTransport_restrict_readsAs (second.restrict store))
    (second.workspaceTransport_restrict_readsAs store)

/-- Restriction through a lexical extension agrees with restriction after the actual Store pop. -/
theorem workspaceTransport_restrict_underWorkspace {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} (transport : Transport outer inner)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    (store : Store (inner.addWorkspace key shape fresh)) :
    (transport.underWorkspace key shape fresh).restrict store =
      transport.restrict (Store.popWorkspace key shape fresh store) := by
  apply (workspaceTransport_readsAs_restrict_iff (transport.underWorkspace key shape fresh)).mp
  apply (workspaceTransport_readsAs_underWorkspace_iff transport key shape fresh).mpr
  exact transport.workspaceTransport_restrict_readsAs _

/-- Restriction commutes with writing the same value to a caller output and its lifted output. -/
theorem workspaceTransport_restrict_write {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} (transport : Transport outer inner) (store : Store inner)
    {shape : CShape} (output : CWriteRef outer shape) (value : shape.Value) :
    transport.restrict (store.write (transport.liftWrite output) value) =
      (transport.restrict store).write output value := by
  apply (workspaceTransport_readsAs_restrict_iff transport).mp
  exact transport.workspaceTransport_readsAs_write
    (transport.workspaceTransport_restrict_readsAs store) output value

end QuantumAlg.Execution.ClassicalWorkspace.Transport
