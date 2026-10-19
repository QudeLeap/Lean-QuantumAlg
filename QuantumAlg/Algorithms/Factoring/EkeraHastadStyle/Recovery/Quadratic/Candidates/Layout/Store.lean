/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Layout
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Actual stores at entry and release of the four candidate words

These are the exact four workspace pushes and reverse pops used by the
candidate layout. Every original source and selector read retains its full
value across entry and release. Candidate initialization itself remains the
actual arithmetic circuit, so none of the caller's values need initialization.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Layout

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Entry follows the same four real workspace allocations as the actual candidate scopes. -/
def pushStore (width : Nat) (store : Store ctx) : Store (context ctx width) :=
  let store1 : Store (centerCtx ctx width) :=
    store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (RSA.quadraticWordWidth width))
      ctx.canonicalFreshKey_fresh
  let store2 : Store (rootCtx ctx width) :=
    store1.pushWorkspace (centerCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) (centerCtx ctx width).canonicalFreshKey_fresh
  let store3 : Store (firstCtx ctx width) :=
    store2.pushWorkspace (rootCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) (rootCtx ctx width).canonicalFreshKey_fresh
  store3.pushWorkspace (firstCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width)) (firstCtx ctx width).canonicalFreshKey_fresh

/-- Release removes exactly the same four workspace heads in reverse order. -/
def popStore (width : Nat) (store : Store (context ctx width)) : Store ctx :=
  let store3 : Store (firstCtx ctx width) :=
    Store.popWorkspace (firstCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) (firstCtx ctx width).canonicalFreshKey_fresh
      store
  let store2 : Store (rootCtx ctx width) :=
    Store.popWorkspace (rootCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) (rootCtx ctx width).canonicalFreshKey_fresh
      store3
  let store1 : Store (centerCtx ctx width) :=
    Store.popWorkspace (centerCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) (centerCtx ctx width).canonicalFreshKey_fresh
      store2
  Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (RSA.quadraticWordWidth width))
    ctx.canonicalFreshKey_fresh store1

/-- The actual four-word entry preserves the complete value of every original structural read. -/
lemma nativeQuadratic_layout_push_read {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) (store : Store ctx) :
    (pushStore width store).read (underRead input width) = store.read input := by
  let ref1 : CInputRef (centerCtx ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) ctx.canonicalFreshKey_fresh
  let ref2 : CInputRef (rootCtx ctx width) shape :=
    ref1.underWorkspace (centerCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) (centerCtx ctx width).canonicalFreshKey_fresh
  let ref3 : CInputRef (firstCtx ctx width) shape :=
    ref2.underWorkspace (rootCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) (rootCtx ctx width).canonicalFreshKey_fresh
  let store1 : Store (centerCtx ctx width) :=
    store.pushWorkspace ctx.canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) ctx.canonicalFreshKey_fresh
  let store2 : Store (rootCtx ctx width) :=
    store1.pushWorkspace (centerCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) (centerCtx ctx width).canonicalFreshKey_fresh
  let store3 : Store (firstCtx ctx width) :=
    store2.pushWorkspace (rootCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) (rootCtx ctx width).canonicalFreshKey_fresh
  exact (Store.read_pushWorkspace_underWorkspace store3 (firstCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    (firstCtx ctx width).canonicalFreshKey_fresh ref3).trans
    ((Store.read_pushWorkspace_underWorkspace store2 (rootCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    (rootCtx ctx width).canonicalFreshKey_fresh ref2).trans
    ((Store.read_pushWorkspace_underWorkspace store1 (centerCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    (centerCtx ctx width).canonicalFreshKey_fresh ref1).trans
    (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width)) ctx.canonicalFreshKey_fresh input)))

/-- Releasing the same words exposes exactly the surviving original structural reads. -/
lemma nativeQuadratic_layout_pop_read {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) (store : Store (context ctx width)) :
    (popStore width store).read input = store.read (underRead input width) := by
  let ref1 : CInputRef (centerCtx ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) ctx.canonicalFreshKey_fresh
  let ref2 : CInputRef (rootCtx ctx width) shape :=
    ref1.underWorkspace (centerCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) (centerCtx ctx width).canonicalFreshKey_fresh
  let ref3 : CInputRef (firstCtx ctx width) shape :=
    ref2.underWorkspace (rootCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) (rootCtx ctx width).canonicalFreshKey_fresh
  let store3 : Store (firstCtx ctx width) :=
    Store.popWorkspace (firstCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width))
      (firstCtx ctx width).canonicalFreshKey_fresh store
  let store2 : Store (rootCtx ctx width) :=
    Store.popWorkspace (rootCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width))
      (rootCtx ctx width).canonicalFreshKey_fresh store3
  let store1 : Store (centerCtx ctx width) :=
    Store.popWorkspace (centerCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width))
      (centerCtx ctx width).canonicalFreshKey_fresh store2
  exact (Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width)) ctx.canonicalFreshKey_fresh store1 input).trans
    ((Store.read_popWorkspace_underWorkspace (centerCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    (centerCtx ctx width).canonicalFreshKey_fresh store2 ref1).trans
    ((Store.read_popWorkspace_underWorkspace (rootCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    (rootCtx ctx width).canonicalFreshKey_fresh store3 ref2).trans
    (Store.read_popWorkspace_underWorkspace (firstCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    (firstCtx ctx width).canonicalFreshKey_fresh store ref3)))

/-- Lifting a real original destination through these four scopes retains its physical key. -/
lemma nativeQuadratic_layout_underWrite_key {shape : CShape}
    (output : CWriteRef ctx shape) (width : Nat) :
    (underWrite output width).key = output.key := rfl

/-- The lifted writable position gives the same structural source read beneath all four words. -/
lemma nativeQuadratic_layout_underWrite_read {shape : CShape}
    (output : CWriteRef ctx shape) (width : Nat) :
    CInputRef.storage (underWrite output width).toCStorageRef =
      underRead (.storage output.toCStorageRef) width := rfl

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Layout
