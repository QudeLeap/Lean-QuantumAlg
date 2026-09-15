/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Permutation.References
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# The same finite store in permuted entry coordinates

Every finite value is read from its original cell. The complete store map is
invertible and commutes with actual reads and writes. Quantum entries retain
only their existing presence markers here; quantum states are never stored,
prepared or transformed by this coordinate correspondence.
-/

namespace QuantumAlg.Execution.ContextPermutation

noncomputable section

variable {kind : ProblemKind} {source target : RuntimeCtx kind}
  (same : source.entries.Perm target.entries)

/-- Express exactly the original finite cells in the target entry order. -/
def store (original : Store source) : Store target :=
  Store.ofValues target fun key role _shape present =>
    original.read (.storage ⟨key, role, slotOfMem (same.mem_iff.mpr present)⟩)

/-- The target's storage read is precisely the original read at the same live entry. -/
theorem store_read_storage (original : Store source) {shape : CShape}
    (ref : CStorageRef source shape) :
    (store same original).read (.storage (storage same ref)) = original.read (.storage ref) := by
  rw [store, Store.read_ofValues]
  congr 2
  exact CStorageRef.storageRef_eq_of_key _ _ rfl

/-- Every compound input read keeps its actual finite value. -/
theorem store_read_input (original : Store source) {shape : CShape}
    (ref : CInputRef source shape) :
    (store same original).read (input same ref) = original.read ref := by
  induction ref with
  | storage ref => exact store_read_storage same original ref
  | product first second firstIH secondIH =>
      exact congrArg₂ CShape.Value.product firstIH secondIH
  | fixedVector refs ih =>
      exact congrArg CShape.Value.fixedVector (funext ih)
  | first ref ih => exact congrArg CShape.Value.first ih
  | second ref ih => exact congrArg CShape.Value.second ih
  | vectorGet ref index ih => exact congrArg (fun value => value.get index) ih
  | bitsGet ref index ih => exact congrArg (fun value => value.bitGet index) ih
  | wordBitGet ref index ih => exact congrArg (fun value => value.wordBitGet index) ih

/-- Reversing the entry permutation recovers every cell of the original store. -/
theorem store_inverse (original : Store source) :
    store same.symm (store same original) = original := by
  apply Store.store_eq_of_storage_reads
  intro shape ref
  rw [← storage_inverse same ref, store_read_storage, store_read_storage, storage_inverse]

/-- Complete finite stores have an exact correspondence with no removed or invented value. -/
def storeEquiv : Store source ≃ Store target where
  toFun := store same
  invFun := store same.symm
  left_inv := store_inverse same
  right_inv := store_inverse same.symm

/-- The same actual write commutes with the change of entry coordinates. -/
theorem store_write (original : Store source) {shape : CShape}
    (output : CWriteRef source shape) (value : CShape.Value shape) :
    store same (original.write output value) =
      (store same original).write (writable same output) value := by
  apply Store.store_eq_write_of_read_frame
  · change (store same (original.write output value)).read
      (.storage (storage same output.toCStorageRef)) = value
    rw [store_read_storage, Store.read_write_same]
  · intro otherShape observed different
    obtain ⟨originalRef, rfl⟩ := storage_surjective same observed
    rw [store_read_storage, store_read_storage]
    exact Store.read_write_other original output originalRef value different

end

end QuantumAlg.Execution.ContextPermutation
