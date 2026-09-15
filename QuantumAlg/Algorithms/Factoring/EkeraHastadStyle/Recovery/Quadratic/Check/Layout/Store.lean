/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check.Layout

/-!
# Actual entry, exit and structural reads of the five checker cells

These maps are precisely the five pushes and reverse pops of the real check
scopes. The zero operand has its actual allocation value. Every lifted source
read and writable reference retains its original physical storage identity;
no premise about the caller's stored values is introduced.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.CheckLayout

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- The five actual workspace pushes, in the same order as the real scoped program. -/
def pushStore (width : Nat) (store : Store ctx) : Store (context ctx width) :=
  let store1 : Store (zeroCtx ctx width) :=
    store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh
  let store2 : Store (upperCtx ctx width) :=
    store1.pushWorkspace (zeroCtx ctx width).canonicalFreshKey .bit
      (zeroCtx ctx width).canonicalFreshKey_fresh
  let store3 : Store (dividesCtx ctx width) :=
    store2.pushWorkspace (upperCtx ctx width).canonicalFreshKey .bit
      (upperCtx ctx width).canonicalFreshKey_fresh
  let store4 : Store (firstCtx ctx width) :=
    store3.pushWorkspace (dividesCtx ctx width).canonicalFreshKey .bit
      (dividesCtx ctx width).canonicalFreshKey_fresh
  store4.pushWorkspace (firstCtx ctx width).canonicalFreshKey .bit
    (firstCtx ctx width).canonicalFreshKey_fresh

/-- Reverse pops expose exactly the original entries surviving the five actual lexical scopes. -/
def popStore (width : Nat) (store : Store (context ctx width)) : Store ctx :=
  let store4 : Store (firstCtx ctx width) :=
    Store.popWorkspace (firstCtx ctx width).canonicalFreshKey .bit
      (firstCtx ctx width).canonicalFreshKey_fresh store
  let store3 : Store (dividesCtx ctx width) :=
    Store.popWorkspace (dividesCtx ctx width).canonicalFreshKey .bit
      (dividesCtx ctx width).canonicalFreshKey_fresh store4
  let store2 : Store (upperCtx ctx width) :=
    Store.popWorkspace (upperCtx ctx width).canonicalFreshKey .bit
      (upperCtx ctx width).canonicalFreshKey_fresh store3
  let store1 : Store (zeroCtx ctx width) :=
    Store.popWorkspace (zeroCtx ctx width).canonicalFreshKey .bit
      (zeroCtx ctx width).canonicalFreshKey_fresh store2
  Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh store1

/-- Structural lifting preserves the complete set of actually read original keys. -/
theorem nativeQuadratic_checkLayout_underRead_keys {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) :
    (underRead input width).storageKeys = input.storageKeys := by
  let ref1 : CInputRef (zeroCtx ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh
  let ref2 : CInputRef (upperCtx ctx width) shape :=
    ref1.underWorkspace (zeroCtx ctx width).canonicalFreshKey .bit
      (zeroCtx ctx width).canonicalFreshKey_fresh
  let ref3 : CInputRef (dividesCtx ctx width) shape :=
    ref2.underWorkspace (upperCtx ctx width).canonicalFreshKey .bit
      (upperCtx ctx width).canonicalFreshKey_fresh
  let ref4 : CInputRef (firstCtx ctx width) shape :=
    ref3.underWorkspace (dividesCtx ctx width).canonicalFreshKey .bit
      (dividesCtx ctx width).canonicalFreshKey_fresh
  exact (CInputRef.storageKeys_underWorkspace ref4
    (firstCtx ctx width).canonicalFreshKey .bit (firstCtx ctx width).canonicalFreshKey_fresh).trans
    ((CInputRef.storageKeys_underWorkspace ref3
    (dividesCtx ctx width).canonicalFreshKey .bit
    (dividesCtx ctx width).canonicalFreshKey_fresh).trans
    ((CInputRef.storageKeys_underWorkspace ref2
    (upperCtx ctx width).canonicalFreshKey .bit (upperCtx ctx width).canonicalFreshKey_fresh).trans
    ((CInputRef.storageKeys_underWorkspace ref1
    (zeroCtx ctx width).canonicalFreshKey .bit (zeroCtx ctx width).canonicalFreshKey_fresh).trans
    ((CInputRef.storageKeys_underWorkspace input
    ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)))))

/-- The five concrete pushes preserve every original structural read completely. -/
theorem nativeQuadratic_checkLayout_push_read {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) (store : Store ctx) :
    (pushStore width store).read (underRead input width) = store.read input := by
  let ref1 : CInputRef (zeroCtx ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh
  let ref2 : CInputRef (upperCtx ctx width) shape :=
    ref1.underWorkspace (zeroCtx ctx width).canonicalFreshKey .bit
      (zeroCtx ctx width).canonicalFreshKey_fresh
  let ref3 : CInputRef (dividesCtx ctx width) shape :=
    ref2.underWorkspace (upperCtx ctx width).canonicalFreshKey .bit
      (upperCtx ctx width).canonicalFreshKey_fresh
  let ref4 : CInputRef (firstCtx ctx width) shape :=
    ref3.underWorkspace (dividesCtx ctx width).canonicalFreshKey .bit
      (dividesCtx ctx width).canonicalFreshKey_fresh
  let store1 : Store (zeroCtx ctx width) :=
    store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh
  let store2 : Store (upperCtx ctx width) :=
    store1.pushWorkspace (zeroCtx ctx width).canonicalFreshKey .bit
      (zeroCtx ctx width).canonicalFreshKey_fresh
  let store3 : Store (dividesCtx ctx width) :=
    store2.pushWorkspace (upperCtx ctx width).canonicalFreshKey .bit
      (upperCtx ctx width).canonicalFreshKey_fresh
  let store4 : Store (firstCtx ctx width) :=
    store3.pushWorkspace (dividesCtx ctx width).canonicalFreshKey .bit
      (dividesCtx ctx width).canonicalFreshKey_fresh
  exact (Store.read_pushWorkspace_underWorkspace store4
    (firstCtx ctx width).canonicalFreshKey .bit
    (firstCtx ctx width).canonicalFreshKey_fresh ref4).trans
    ((Store.read_pushWorkspace_underWorkspace store3
    (dividesCtx ctx width).canonicalFreshKey .bit
    (dividesCtx ctx width).canonicalFreshKey_fresh ref3).trans
    ((Store.read_pushWorkspace_underWorkspace store2
    (upperCtx ctx width).canonicalFreshKey .bit
    (upperCtx ctx width).canonicalFreshKey_fresh ref2).trans
    ((Store.read_pushWorkspace_underWorkspace store1
    (zeroCtx ctx width).canonicalFreshKey .bit
    (zeroCtx ctx width).canonicalFreshKey_fresh ref1).trans
    ((Store.read_pushWorkspace_underWorkspace store
    ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh input)))))

/-- The five reverse releases preserve exactly the surviving original structural reads. -/
theorem nativeQuadratic_checkLayout_pop_read {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) (store : Store (context ctx width)) :
    (popStore width store).read input = store.read (underRead input width) := by
  let ref1 : CInputRef (zeroCtx ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh
  let ref2 : CInputRef (upperCtx ctx width) shape :=
    ref1.underWorkspace (zeroCtx ctx width).canonicalFreshKey .bit
      (zeroCtx ctx width).canonicalFreshKey_fresh
  let ref3 : CInputRef (dividesCtx ctx width) shape :=
    ref2.underWorkspace (upperCtx ctx width).canonicalFreshKey .bit
      (upperCtx ctx width).canonicalFreshKey_fresh
  let ref4 : CInputRef (firstCtx ctx width) shape :=
    ref3.underWorkspace (dividesCtx ctx width).canonicalFreshKey .bit
      (dividesCtx ctx width).canonicalFreshKey_fresh
  let store4 : Store (firstCtx ctx width) :=
    Store.popWorkspace (firstCtx ctx width).canonicalFreshKey .bit
      (firstCtx ctx width).canonicalFreshKey_fresh store
  let store3 : Store (dividesCtx ctx width) :=
    Store.popWorkspace (dividesCtx ctx width).canonicalFreshKey .bit
      (dividesCtx ctx width).canonicalFreshKey_fresh store4
  let store2 : Store (upperCtx ctx width) :=
    Store.popWorkspace (upperCtx ctx width).canonicalFreshKey .bit
      (upperCtx ctx width).canonicalFreshKey_fresh store3
  let store1 : Store (zeroCtx ctx width) :=
    Store.popWorkspace (zeroCtx ctx width).canonicalFreshKey .bit
      (zeroCtx ctx width).canonicalFreshKey_fresh store2
  exact (Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh store1 input).trans
    ((Store.read_popWorkspace_underWorkspace (zeroCtx ctx width).canonicalFreshKey .bit
    (zeroCtx ctx width).canonicalFreshKey_fresh store2 ref1).trans
    ((Store.read_popWorkspace_underWorkspace (upperCtx ctx width).canonicalFreshKey .bit
    (upperCtx ctx width).canonicalFreshKey_fresh store3 ref2).trans
    ((Store.read_popWorkspace_underWorkspace (dividesCtx ctx width).canonicalFreshKey .bit
    (dividesCtx ctx width).canonicalFreshKey_fresh store4 ref3).trans
    ((Store.read_popWorkspace_underWorkspace (firstCtx ctx width).canonicalFreshKey .bit
    (firstCtx ctx width).canonicalFreshKey_fresh store ref4)))))

/-- The actual fresh zero word has its declared zero value before either check runs. -/
theorem nativeQuadratic_checkLayout_push_zero (width : Nat) (store : Store ctx) :
    (pushStore width store).read (.storage (zero ctx width).toCStorageRef) =
      CShape.wordOfNat width 0 := rfl

/-- The actual zero's unsigned read is zero also at width zero. -/
theorem nativeQuadratic_checkLayout_push_zero_toNat (width : Nat) (store : Store ctx) :
    ((pushStore width store).read (.storage (zero ctx width).toCStorageRef)).toNat = 0 := by
  rw [nativeQuadratic_checkLayout_push_zero]
  exact Nat.zero_mod _

/-- Actual write-reference lifting retains the same original storage identity. -/
theorem nativeQuadratic_checkLayout_underWrite_key {shape : CShape}
    (output : CWriteRef ctx shape) (width : Nat) :
    (underWrite output width).key = output.key := rfl

/-- Reading a lifted destination is the same closed structural read beneath the five entries. -/
theorem nativeQuadratic_checkLayout_underWrite_read {shape : CShape}
    (output : CWriteRef ctx shape) (width : Nat) :
    CInputRef.storage (underWrite output width).toCStorageRef =
      underRead (.storage output.toCStorageRef) width := rfl

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.CheckLayout
