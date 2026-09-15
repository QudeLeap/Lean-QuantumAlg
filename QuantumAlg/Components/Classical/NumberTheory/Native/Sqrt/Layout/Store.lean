/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Separation

/-!
# Actual square-root scope entry and exit stores

These maps are exactly the six workspace pushes and six matching pops of
`into`. Their structural read laws preserve arbitrary caller values across
the real scopes. The root's zero is the actual fresh allocation value; no
initialization assumption is imposed on the caller's storage.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- The six actual workspace pushes used by the native routine. -/
def pushStore (width : Nat) (store : Store ctx) : Store (context ctx width) :=
  let store1 : Store (wideContext ctx width) :=
    store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
      ctx.canonicalFreshKey_fresh
  let store2 : Store (rootContext ctx width) :=
    store1.pushWorkspace (wideContext ctx width).canonicalFreshKey (.unsignedWord width)
      (wideContext ctx width).canonicalFreshKey_fresh
  let store3 : Store (halfContext ctx width) :=
    store2.pushWorkspace (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
      (rootContext ctx width).canonicalFreshKey_fresh
  let store4 : Store (candidateContext ctx width) :=
    store3.pushWorkspace (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
      (halfContext ctx width).canonicalFreshKey_fresh
  let store5 : Store (squareContext ctx width) :=
    store4.pushWorkspace (candidateContext ctx width).canonicalFreshKey
      (.unsignedWord (width + width))
      (candidateContext ctx width).canonicalFreshKey_fresh
  let store6 : Store (context ctx width) :=
    store5.pushWorkspace (squareContext ctx width).canonicalFreshKey .bit
      (squareContext ctx width).canonicalFreshKey_fresh
  store6

/-- The six actual reverse releases used by the same native routine. -/
def popStore (width : Nat) (store : Store (context ctx width)) : Store ctx :=
  let store5 : Store (squareContext ctx width) :=
    Store.popWorkspace (squareContext ctx width).canonicalFreshKey .bit
      (squareContext ctx width).canonicalFreshKey_fresh store
  let store4 : Store (candidateContext ctx width) :=
    Store.popWorkspace (candidateContext ctx width).canonicalFreshKey
      (.unsignedWord (width + width))
      (candidateContext ctx width).canonicalFreshKey_fresh store5
  let store3 : Store (halfContext ctx width) :=
    Store.popWorkspace (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
      (halfContext ctx width).canonicalFreshKey_fresh store4
  let store2 : Store (rootContext ctx width) :=
    Store.popWorkspace (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
      (rootContext ctx width).canonicalFreshKey_fresh store3
  let store1 : Store (wideContext ctx width) :=
    Store.popWorkspace (wideContext ctx width).canonicalFreshKey (.unsignedWord width)
      (wideContext ctx width).canonicalFreshKey_fresh store2
  Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh store1

/-- Every lifted structural reference traverses precisely its original stored keys. -/
theorem nativeSqrt_underRead_keys {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) : (underRead input width).storageKeys = input.storageKeys := by
  let ref1 : CInputRef (wideContext ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
      ctx.canonicalFreshKey_fresh
  let ref2 : CInputRef (rootContext ctx width) shape :=
    ref1.underWorkspace (wideContext ctx width).canonicalFreshKey (.unsignedWord width)
      (wideContext ctx width).canonicalFreshKey_fresh
  let ref3 : CInputRef (halfContext ctx width) shape :=
    ref2.underWorkspace (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
      (rootContext ctx width).canonicalFreshKey_fresh
  let ref4 : CInputRef (candidateContext ctx width) shape :=
    ref3.underWorkspace (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
      (halfContext ctx width).canonicalFreshKey_fresh
  let ref5 : CInputRef (squareContext ctx width) shape :=
    ref4.underWorkspace (candidateContext ctx width).canonicalFreshKey
      (.unsignedWord (width + width))
      (candidateContext ctx width).canonicalFreshKey_fresh
  exact (CInputRef.storageKeys_underWorkspace ref5
    (squareContext ctx width).canonicalFreshKey .bit
    (squareContext ctx width).canonicalFreshKey_fresh).trans
    ((CInputRef.storageKeys_underWorkspace ref4
    (candidateContext ctx width).canonicalFreshKey
      (.unsignedWord (width + width))
    (candidateContext ctx width).canonicalFreshKey_fresh).trans
    ((CInputRef.storageKeys_underWorkspace ref3
    (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
    (halfContext ctx width).canonicalFreshKey_fresh).trans
    ((CInputRef.storageKeys_underWorkspace ref2
    (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
    (rootContext ctx width).canonicalFreshKey_fresh).trans
    ((CInputRef.storageKeys_underWorkspace ref1
    (wideContext ctx width).canonicalFreshKey (.unsignedWord width)
    (wideContext ctx width).canonicalFreshKey_fresh).trans
    ((CInputRef.storageKeys_underWorkspace input
    ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh))))))

/-- Entering all actual scopes preserves every original structured input exactly. -/
theorem nativeSqrt_push_read {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) (store : Store ctx) :
    (pushStore width store).read (underRead input width) = store.read input := by
  let ref1 : CInputRef (wideContext ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
      ctx.canonicalFreshKey_fresh
  let ref2 : CInputRef (rootContext ctx width) shape :=
    ref1.underWorkspace (wideContext ctx width).canonicalFreshKey (.unsignedWord width)
      (wideContext ctx width).canonicalFreshKey_fresh
  let ref3 : CInputRef (halfContext ctx width) shape :=
    ref2.underWorkspace (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
      (rootContext ctx width).canonicalFreshKey_fresh
  let ref4 : CInputRef (candidateContext ctx width) shape :=
    ref3.underWorkspace (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
      (halfContext ctx width).canonicalFreshKey_fresh
  let ref5 : CInputRef (squareContext ctx width) shape :=
    ref4.underWorkspace (candidateContext ctx width).canonicalFreshKey
      (.unsignedWord (width + width))
      (candidateContext ctx width).canonicalFreshKey_fresh
  let store1 : Store (wideContext ctx width) :=
    store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
      ctx.canonicalFreshKey_fresh
  let store2 : Store (rootContext ctx width) :=
    store1.pushWorkspace (wideContext ctx width).canonicalFreshKey (.unsignedWord width)
      (wideContext ctx width).canonicalFreshKey_fresh
  let store3 : Store (halfContext ctx width) :=
    store2.pushWorkspace (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
      (rootContext ctx width).canonicalFreshKey_fresh
  let store4 : Store (candidateContext ctx width) :=
    store3.pushWorkspace (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
      (halfContext ctx width).canonicalFreshKey_fresh
  let store5 : Store (squareContext ctx width) :=
    store4.pushWorkspace (candidateContext ctx width).canonicalFreshKey
      (.unsignedWord (width + width))
      (candidateContext ctx width).canonicalFreshKey_fresh
  exact (Store.read_pushWorkspace_underWorkspace store5
    (squareContext ctx width).canonicalFreshKey .bit
    (squareContext ctx width).canonicalFreshKey_fresh ref5).trans
    ((Store.read_pushWorkspace_underWorkspace store4
    (candidateContext ctx width).canonicalFreshKey
      (.unsignedWord (width + width))
    (candidateContext ctx width).canonicalFreshKey_fresh ref4).trans
    ((Store.read_pushWorkspace_underWorkspace store3
    (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
    (halfContext ctx width).canonicalFreshKey_fresh ref3).trans
    ((Store.read_pushWorkspace_underWorkspace store2
    (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
    (rootContext ctx width).canonicalFreshKey_fresh ref2).trans
    ((Store.read_pushWorkspace_underWorkspace store1
    (wideContext ctx width).canonicalFreshKey (.unsignedWord width)
    (wideContext ctx width).canonicalFreshKey_fresh ref1).trans
    ((Store.read_pushWorkspace_underWorkspace store
    ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh input))))))

/-- Leaving all actual scopes exposes the final original-cell value without changing it. -/
theorem nativeSqrt_pop_read {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) (store : Store (context ctx width)) :
    (popStore width store).read input = store.read (underRead input width) := by
  let ref1 : CInputRef (wideContext ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
      ctx.canonicalFreshKey_fresh
  let ref2 : CInputRef (rootContext ctx width) shape :=
    ref1.underWorkspace (wideContext ctx width).canonicalFreshKey (.unsignedWord width)
      (wideContext ctx width).canonicalFreshKey_fresh
  let ref3 : CInputRef (halfContext ctx width) shape :=
    ref2.underWorkspace (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
      (rootContext ctx width).canonicalFreshKey_fresh
  let ref4 : CInputRef (candidateContext ctx width) shape :=
    ref3.underWorkspace (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
      (halfContext ctx width).canonicalFreshKey_fresh
  let ref5 : CInputRef (squareContext ctx width) shape :=
    ref4.underWorkspace (candidateContext ctx width).canonicalFreshKey
      (.unsignedWord (width + width))
      (candidateContext ctx width).canonicalFreshKey_fresh
  let store5 : Store (squareContext ctx width) :=
    Store.popWorkspace (squareContext ctx width).canonicalFreshKey .bit
      (squareContext ctx width).canonicalFreshKey_fresh store
  let store4 : Store (candidateContext ctx width) :=
    Store.popWorkspace (candidateContext ctx width).canonicalFreshKey
      (.unsignedWord (width + width))
      (candidateContext ctx width).canonicalFreshKey_fresh store5
  let store3 : Store (halfContext ctx width) :=
    Store.popWorkspace (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
      (halfContext ctx width).canonicalFreshKey_fresh store4
  let store2 : Store (rootContext ctx width) :=
    Store.popWorkspace (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
      (rootContext ctx width).canonicalFreshKey_fresh store3
  let store1 : Store (wideContext ctx width) :=
    Store.popWorkspace (wideContext ctx width).canonicalFreshKey (.unsignedWord width)
      (wideContext ctx width).canonicalFreshKey_fresh store2
  exact (Store.read_popWorkspace_underWorkspace
    ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh store1 input).trans
    ((Store.read_popWorkspace_underWorkspace
    (wideContext ctx width).canonicalFreshKey (.unsignedWord width)
    (wideContext ctx width).canonicalFreshKey_fresh store2 ref1).trans
    ((Store.read_popWorkspace_underWorkspace
    (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
    (rootContext ctx width).canonicalFreshKey_fresh store3 ref2).trans
    ((Store.read_popWorkspace_underWorkspace
    (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
    (halfContext ctx width).canonicalFreshKey_fresh store4 ref3).trans
    ((Store.read_popWorkspace_underWorkspace
    (candidateContext ctx width).canonicalFreshKey
      (.unsignedWord (width + width))
    (candidateContext ctx width).canonicalFreshKey_fresh store5 ref4).trans
    ((Store.read_popWorkspace_underWorkspace
    (squareContext ctx width).canonicalFreshKey .bit
    (squareContext ctx width).canonicalFreshKey_fresh store ref5))))))

/-- The root's initial zero comes from its actual fresh lexical allocation. -/
theorem nativeSqrt_push_root_zero (width : Nat) (store : Store ctx) :
    ((pushStore width store).read (.storage (rootCell ctx width).toCStorageRef)).toNat = 0 :=
  rfl

/-- Lifting a writable output preserves its actual stored identity. -/
theorem nativeSqrt_underWrite_key {shape : CShape} (output : CWriteRef ctx shape)
    (width : Nat) : (underWrite output width).key = output.key := rfl

/-- Reading a lifted writable output is the same structural lift as any other original input. -/
theorem nativeSqrt_underWrite_read {shape : CShape} (output : CWriteRef ctx shape)
    (width : Nat) :
    (.storage (underWrite output width).toCStorageRef : CInputRef (context ctx width) shape) =
      underRead (.storage output.toCStorageRef) width := rfl

/-- Every new scratch key is disjoint from every actual original structured input. -/
theorem nativeSqrt_underRead_free {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) (key : StorageKey) (internal : key ∈ internalKeys ctx width) :
    key ∉ (underRead input width).storageKeys := by
  rw [nativeSqrt_underRead_keys]
  intro present
  exact List.disjoint_left.mp (nativeSqrt_internalKeys_disjoint ctx width) internal
    (input.storageKeys_subset_context present)

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
