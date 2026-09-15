/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Row.Layout

/-!
# Intrinsic initialization and read preservation for actual lattice rows

Actual allocation supplies the three zero words and their distinct storage
identities. Original structural inputs are preserved across both entry and
release. These facts discharge the local loader's positional and initial
value conditions inside the real row scope.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.RowLayout

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- The exact three row keys appear in reverse allocation order at the actual context head. -/
def internalKeys (ctx : RuntimeCtx kind) (width : Nat) : List StorageKey :=
  [(refs ctx width).third.key, (refs ctx width).second.key, (refs ctx width).first.key]

/-- The actual row context contains precisely its three new cells and the original entries. -/
theorem nativeLattice_row_keys (ctx : RuntimeCtx kind) (width : Nat) :
    (context ctx width).keys = internalKeys ctx width ++ ctx.keys := rfl

/-- The intrinsic live context proves that the three actual row cells are distinct. -/
theorem nativeLattice_row_nodup (ctx : RuntimeCtx kind) (width : Nat) :
    (internalKeys ctx width).Nodup := by
  have unique := (context ctx width).keysNodup
  change (context ctx width).keys.Nodup at unique
  rw [nativeLattice_row_keys] at unique
  exact (List.nodup_append.mp unique).1

/-- None of the three row cells is an original source or persistent result cell. -/
theorem nativeLattice_row_disjoint (ctx : RuntimeCtx kind) (width : Nat) :
    List.Disjoint (internalKeys ctx width) ctx.keys := by
  have unique := (context ctx width).keysNodup
  change (context ctx width).keys.Nodup at unique
  rw [nativeLattice_row_keys] at unique
  apply List.disjoint_left.mpr
  intro key internal external
  exact (List.nodup_append.mp unique).2.2 key internal key external rfl

/-- Structural lifting retains the exact key support of every original input. -/
theorem nativeLattice_row_underRead_keys {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) :
    (underRead input width).storageKeys = input.storageKeys := by
  let first : CInputRef (context1 ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
  let second : CInputRef (context2 ctx width) shape :=
    first.underWorkspace (context1 ctx width).canonicalFreshKey (.unsignedWord width)
      (context1 ctx width).canonicalFreshKey_fresh
  exact (CInputRef.storageKeys_underWorkspace second (context2 ctx width).canonicalFreshKey
    (.unsignedWord width) (context2 ctx width).canonicalFreshKey_fresh).trans
    ((CInputRef.storageKeys_underWorkspace first (context1 ctx width).canonicalFreshKey
      (.unsignedWord width) (context1 ctx width).canonicalFreshKey_fresh).trans
      (CInputRef.storageKeys_underWorkspace input ctx.canonicalFreshKey
        (.unsignedWord width) ctx.canonicalFreshKey_fresh))

/-- Actual entry preserves the value of every original structural input. -/
theorem nativeLattice_row_push_read {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) (store : Store ctx) :
    (pushStore width store).read (underRead input width) = store.read input := by
  let firstRef : CInputRef (context1 ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
  let secondRef : CInputRef (context2 ctx width) shape :=
    firstRef.underWorkspace (context1 ctx width).canonicalFreshKey (.unsignedWord width)
      (context1 ctx width).canonicalFreshKey_fresh
  let first : Store (context1 ctx width) :=
    store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
  let second : Store (context2 ctx width) :=
    first.pushWorkspace (context1 ctx width).canonicalFreshKey (.unsignedWord width)
      (context1 ctx width).canonicalFreshKey_fresh
  exact (Store.read_pushWorkspace_underWorkspace second (context2 ctx width).canonicalFreshKey
    (.unsignedWord width) (context2 ctx width).canonicalFreshKey_fresh secondRef).trans
    ((Store.read_pushWorkspace_underWorkspace first (context1 ctx width).canonicalFreshKey
      (.unsignedWord width) (context1 ctx width).canonicalFreshKey_fresh firstRef).trans
      (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
        (.unsignedWord width) ctx.canonicalFreshKey_fresh input))

/-- Actual release exposes exactly the corresponding original read in the live row context. -/
theorem nativeLattice_row_pop_read {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) (store : Store (context ctx width)) :
    (popStore width store).read input = store.read (underRead input width) := by
  let firstRef : CInputRef (context1 ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
  let secondRef : CInputRef (context2 ctx width) shape :=
    firstRef.underWorkspace (context1 ctx width).canonicalFreshKey (.unsignedWord width)
      (context1 ctx width).canonicalFreshKey_fresh
  let second : Store (context2 ctx width) :=
    Store.popWorkspace (context2 ctx width).canonicalFreshKey (.unsignedWord width)
      (context2 ctx width).canonicalFreshKey_fresh store
  let first : Store (context1 ctx width) :=
    Store.popWorkspace (context1 ctx width).canonicalFreshKey (.unsignedWord width)
      (context1 ctx width).canonicalFreshKey_fresh second
  exact (Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey
    (.unsignedWord width) ctx.canonicalFreshKey_fresh first input).trans
    ((Store.read_popWorkspace_underWorkspace (context1 ctx width).canonicalFreshKey
      (.unsignedWord width) (context1 ctx width).canonicalFreshKey_fresh second firstRef).trans
      (Store.read_popWorkspace_underWorkspace (context2 ctx width).canonicalFreshKey
        (.unsignedWord width) (context2 ctx width).canonicalFreshKey_fresh store secondRef))

/-- Actual allocation, rather than a caller premise, supplies zero in all three row coordinates. -/
theorem nativeLattice_row_initial_zero (width : Nat) (store : Store ctx) :
    ((pushStore width store).read (.storage (refs ctx width).first.toCStorageRef)).toNat = 0 ∧
      ((pushStore width store).read (.storage (refs ctx width).second.toCStorageRef)).toNat = 0 ∧
      ((pushStore width store).read (.storage (refs ctx width).third.toCStorageRef)).toNat = 0 := by
  exact ⟨rfl, rfl, rfl⟩

private def cellKey (ctx : RuntimeCtx kind) (width : Nat) (index : Fin 3) : StorageKey :=
  (internalKeys ctx width).get ⟨index.val, by change index.val < 3; exact index.isLt⟩

private theorem cellKey_ne (ctx : RuntimeCtx kind) (width : Nat)
    (left right : Fin 3) (different : left ≠ right) :
    cellKey ctx width left ≠ cellKey ctx width right := by
  intro same
  have positions := (nativeLattice_row_nodup ctx width).injective_get same
  exact different (Fin.ext (congrArg Fin.val positions))

/-- The three positional conditions of the literal row loader follow from actual allocation. -/
theorem nativeLattice_row_separated (ctx : RuntimeCtx kind) (width : Nat) :
    (refs ctx width).first.key ≠ (refs ctx width).second.key ∧
      (refs ctx width).first.key ≠ (refs ctx width).third.key ∧
      (refs ctx width).second.key ≠ (refs ctx width).third.key :=
  ⟨cellKey_ne ctx width 2 1 (by decide), cellKey_ne ctx width 2 0 (by decide),
    cellKey_ne ctx width 1 0 (by decide)⟩

/-- Every original source avoids each actual row destination by intrinsic key separation. -/
theorem nativeLattice_row_source_free {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) (key : StorageKey)
    (internal : key ∈ internalKeys ctx width) :
    key ∉ (underRead input width).storageKeys := by
  rw [nativeLattice_row_underRead_keys]
  intro present
  exact List.disjoint_left.mp (nativeLattice_row_disjoint ctx width) internal
    (input.storageKeys_subset_context present)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.RowLayout
