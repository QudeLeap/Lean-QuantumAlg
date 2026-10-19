/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Layout
import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Exact original-store preservation by every reset scratch write

The parent store is recovered by popping precisely its fresh scalar scopes.
Every original storage reference crosses these scopes at the same identity.
Consequently writing any actual scratch outcome preserves the complete
original store, including borrowed, retained, and preexisting workspace cells.
-/

namespace QuantumAlg.ZReset.BankParallel.Workspace

open Execution

variable {kind : ProblemKind}

/-- Remove exactly the scalar scopes owned by the reset parent. -/
def forgetStore (ctx : RuntimeCtx kind) : (count : Nat) → Store (context ctx count) → Store ctx
  | 0, store => store
  | count + 1, store =>
      forgetStore ctx count (Store.popWorkspace (context ctx count).canonicalFreshKey
        (.finite 2) (context ctx count).canonicalFreshKey_fresh store)

/-- Every original readable cell remains at its actual slot under the scratch scopes. -/
def liftStorage {ctx : RuntimeCtx kind} {shape : CShape} (ref : CStorageRef ctx shape) :
    (count : Nat) → CStorageRef (context ctx count) shape
  | 0 => ref
  | count + 1 =>
      (liftStorage ref count).underWorkspace (context ctx count).canonicalFreshKey
        (.finite 2) (context ctx count).canonicalFreshKey_fresh

private lemma storage_key_mem {ctx : RuntimeCtx kind} {shape : CShape}
    (ref : CStorageRef ctx shape) : ref.key ∈ ctx.keys :=
  List.mem_map.mpr ⟨.storage ref.key ref.role shape, ref.present, rfl⟩

/-- A scratch outcome never aliases any original storage cell. -/
lemma reference_ne_liftStorage {ctx : RuntimeCtx kind} {shape : CShape}
    (ref : CStorageRef ctx shape) (count : Nat) (index : Fin count) :
    (reference ctx count index).key ≠ (liftStorage ref count).key := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun previous => ?_) index
      · change (context ctx count).canonicalFreshKey ≠ (liftStorage ref count).key
        intro same
        exact (context ctx count).canonicalFreshKey_fresh
          (same.symm ▸ storage_key_mem (liftStorage ref count))
      · exact ih previous

/-- Recovering the parent store exposes precisely its original cell values. -/
lemma forgetStore_read {ctx : RuntimeCtx kind} {shape : CShape}
    (ref : CStorageRef ctx shape) (count : Nat) (store : Store (context ctx count)) :
    (forgetStore ctx count store).read (.storage ref) =
      store.read (.storage (liftStorage ref count)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [forgetStore, ih, Store.read_popWorkspace_underWorkspace]
      rfl

/-- Writing an actual scratch key preserves every original cell and hence the complete store. -/
lemma forgetStore_write {ctx : RuntimeCtx kind} {shape : CShape}
    (count : Nat) (output : CWriteRef (context ctx count) shape)
    (scratch : ∃ index, output.key = (reference ctx count index).key)
    (store : Store (context ctx count)) (value : shape.Value) :
    forgetStore ctx count (store.write output value) = forgetStore ctx count store := by
  apply Store.store_eq_of_storage_reads
  intro observedShape observed
  rw [forgetStore_read, forgetStore_read]
  apply Store.read_write_other
  obtain ⟨index, same⟩ := scratch
  rw [same]
  exact reference_ne_liftStorage observed count index

end QuantumAlg.ZReset.BankParallel.Workspace
