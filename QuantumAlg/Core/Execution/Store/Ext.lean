/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Store

/-!
# Extensionality of the actual finite classical store

The existing typed storage reads determine all classical cells. Quantum
entries have only their presence markers in this store; their joint state
continues to live in the separate execution-state blocks. Unique runtime
keys identify the same stored shape and computational slot. Consequently,
an output value and the unchanged reads of all other cells determine the
exact result of one mathematical write, independently of its computation.
-/

namespace QuantumAlg

private lemma entrySlot_unique {kind : ProblemKind} {entry : RuntimeEntry kind}
    {entries : List (RuntimeEntry kind)} (first second : RuntimeEntrySlot entry entries)
    (unique : entries.Nodup) : first = second := by
  induction first with
  | here =>
      cases second with
      | here => rfl
      | there next => exact False.elim ((List.nodup_cons.mp unique).1 next.toMem)
  | there next ih =>
      cases second with
      | here => exact False.elim ((List.nodup_cons.mp unique).1 next.toMem)
      | there other =>
          exact congrArg RuntimeEntrySlot.there (ih other (List.nodup_cons.mp unique).2)

namespace CStorageRef

/-- A unique live key carries exactly one stored shape, even across differently typed references. -/
lemma storageRef_shape_eq_of_key {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {firstShape secondShape : CShape} (first : CStorageRef ctx firstShape)
    (second : CStorageRef ctx secondShape) (same : first.key = second.key) :
    firstShape = secondShape := by
  have entries := List.inj_on_of_nodup_map ctx.keysNodup first.present second.present same
  exact (RuntimeEntry.storage.inj entries).2.2

/-- Same-shaped references with the same live key denote the identical computational slot. -/
lemma storageRef_eq_of_key {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (first second : CStorageRef ctx shape) (same : first.key = second.key) : first = second := by
  obtain ⟨firstKey, firstRole, firstSlot⟩ := first
  obtain ⟨secondKey, secondRole, secondSlot⟩ := second
  change firstKey = secondKey at same
  cases same
  have entries := List.inj_on_of_nodup_map ctx.keysNodup firstSlot.toMem secondSlot.toMem rfl
  have roles : firstRole = secondRole := (RuntimeEntry.storage.inj entries).2.1
  cases roles
  have slots := entrySlot_unique firstSlot secondSlot (List.Nodup.of_map _ ctx.keysNodup)
  cases slots
  rfl

end CStorageRef

namespace Execution

private lemma cells_eq_of_storage_reads {kind : ProblemKind}
    {entries : List (RuntimeEntry kind)} (first second : Cells entries)
    (equal : ∀ key role shape (slot : RuntimeEntrySlot (.storage key role shape) entries),
      Cells.read first slot = Cells.read second slot) : first = second := by
  induction entries with
  | nil => exact Subsingleton.elim (α := Unit) _ _
  | cons entry tail ih =>
      apply Prod.ext
      · cases entry with
        | storage key role shape => exact equal key role shape .here
        | borrowedLayout key layout => exact Subsingleton.elim (α := Unit) _ _
        | suppliedLayout key layout => exact Subsingleton.elim (α := Unit) _ _
        | ownedLayout key layout => exact Subsingleton.elim (α := Unit) _ _
        | ownedCopies key bank => exact Subsingleton.elim (α := Unit) _ _
      · exact ih first.2 second.2 (fun key role shape slot => equal key role shape (.there slot))

namespace Store

/-- All actual storage reads determine the complete finite store. -/
lemma store_eq_of_storage_reads {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (first second : Store ctx)
    (equal : ∀ {shape : CShape} (input : CStorageRef ctx shape),
      first.read (.storage input) = second.read (.storage input)) : first = second := by
  obtain ⟨first⟩ := first
  obtain ⟨second⟩ := second
  exact congrArg Store.mk (cells_eq_of_storage_reads first second
    (fun key role shape slot => equal ⟨key, role, slot⟩))

/-- A computed output and the exact frame of every other cell determine one complete write. -/
lemma store_eq_write_of_read_frame {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (before after : Store ctx) (output : CWriteRef ctx shape)
    (value : shape.Value) (written : after.read (.storage output.toCStorageRef) = value)
    (unchanged : ∀ {otherShape : CShape} (other : CStorageRef ctx otherShape),
      output.key ≠ other.key → after.read (.storage other) = before.read (.storage other)) :
    after = before.write output value := by
  apply store_eq_of_storage_reads
  intro otherShape other
  classical
  by_cases same : output.key = other.key
  · have shapes : shape = otherShape :=
      CStorageRef.storageRef_shape_eq_of_key output.toCStorageRef other same
    cases shapes
    have refs : output.toCStorageRef = other :=
      CStorageRef.storageRef_eq_of_key output.toCStorageRef other same
    cases refs
    exact written.trans (read_write_same before output value).symm
  · exact (unchanged other same).trans (read_write_other before output other value same).symm

end Store
end Execution
end QuantumAlg
