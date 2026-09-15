/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Union.References
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Identical live references under an entry permutation

The two contexts contain exactly the same entries, including each storage key,
role, shape and physical quantum layout. These maps change only computational
positions in the entry list. They do not allocate a cell, change ownership,
compute a stored value or execute a physical operation.
-/

namespace QuantumAlg.Execution.ContextPermutation

noncomputable section

private theorem slot_exists {kind : ProblemKind} {entry : RuntimeEntry kind}
    {entries : List (RuntimeEntry kind)} (present : entry ∈ entries) :
    Nonempty (RuntimeEntrySlot entry entries) := by
  induction entries with
  | nil => cases present
  | cons head tail ih =>
      rcases List.mem_cons.mp present with same | later
      · subst head
        exact ⟨.here⟩
      · obtain ⟨slot⟩ := ih later
        exact ⟨.there slot⟩

private def slotOfMem {kind : ProblemKind} {entry : RuntimeEntry kind}
    {entries : List (RuntimeEntry kind)} (present : entry ∈ entries) :
    RuntimeEntrySlot entry entries :=
  Classical.choice (slot_exists present)

variable {kind : ProblemKind} {source target : RuntimeCtx kind}
  (same : source.entries.Perm target.entries)

/-- Select the same live cell, with exactly its original key, role and shape. -/
def storage {shape : CShape} (ref : CStorageRef source shape) : CStorageRef target shape where
  key := ref.key
  role := ref.role
  slot := slotOfMem (same.mem_iff.mp ref.present)

/-- Reindexing a writable reference preserves its original write permission. -/
def writable {shape : CShape} (ref : CWriteRef source shape) : CWriteRef target shape where
  toCStorageRef := storage same ref.toCStorageRef
  writable := ref.writable

/-- Products, projections and bit reads retain their original structural operands. -/
def input {shape : CShape} (ref : CInputRef source shape) : CInputRef target shape :=
  ContextUnion.mapInput (storage same) ref

@[simp] theorem storage_key {shape : CShape} (ref : CStorageRef source shape) :
    (storage same ref).key = ref.key := rfl

@[simp] theorem storage_role {shape : CShape} (ref : CStorageRef source shape) :
    (storage same ref).role = ref.role := rfl

@[simp] theorem writable_key {shape : CShape} (ref : CWriteRef source shape) :
    (writable same ref).key = ref.key := rfl

@[simp] theorem writable_role {shape : CShape} (ref : CWriteRef source shape) :
    (writable same ref).role = ref.role := rfl

/-- A round trip returns the identical source reference, including its computational slot. -/
theorem storage_inverse {shape : CShape} (ref : CStorageRef source shape) :
    storage same.symm (storage same ref) = ref :=
  CStorageRef.storageRef_eq_of_key _ _ rfl

/-- Every target storage reference comes from its identical source entry. -/
theorem storage_surjective {shape : CShape} :
    Function.Surjective (storage same (shape := shape)) := by
  intro ref
  exact ⟨storage same.symm ref, storage_inverse same.symm ref⟩

/-- A writable round trip preserves the complete original permission-bearing reference. -/
theorem writable_inverse {shape : CShape} (ref : CWriteRef source shape) :
    writable same.symm (writable same ref) = ref := by
  cases ref with
  | mk ref permission =>
      simpa only [writable, CWriteRef.mk.injEq] using storage_inverse same ref

end

end QuantumAlg.Execution.ContextPermutation
