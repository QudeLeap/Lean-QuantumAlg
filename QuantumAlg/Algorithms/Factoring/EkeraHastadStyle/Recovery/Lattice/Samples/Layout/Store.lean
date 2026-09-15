/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Samples.Layout

/-!
# Intrinsic storage separation and reads of the actual sample layout

The context's own key uniqueness proves that all four sample destinations
differ and avoid every original source. Entry and reverse release preserve
each original structural read. These facts discharge positional requirements
inside the real pair layout, without adding caller aliasing conditions.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.SampleLayout

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {m ell : Nat}

/-- The four actual keys in final stack order, from the second k back to the first j. -/
def internalKeys (ctx : RuntimeCtx kind) (m ell : Nat) : List StorageKey :=
  [(secondRefs ctx m ell).k.key, (secondRefs ctx m ell).j.key,
    (firstRefs ctx m ell).k.key, (firstRefs ctx m ell).j.key]

/-- The final context has exactly these four additional cells and the original entries. -/
theorem nativeLattice_sample_keys (ctx : RuntimeCtx kind) (m ell : Nat) :
    (context ctx m ell).keys = internalKeys ctx m ell ++ ctx.keys := rfl

/-- The intrinsic context proves that all actual sample destinations are distinct. -/
theorem nativeLattice_sample_nodup (ctx : RuntimeCtx kind) (m ell : Nat) :
    (internalKeys ctx m ell).Nodup := by
  have unique := (context ctx m ell).keysNodup
  change (context ctx m ell).keys.Nodup at unique
  rw [nativeLattice_sample_keys] at unique
  exact (List.nodup_append.mp unique).1

/-- None of the newly allocated sample cells is an existing storage entry. -/
theorem nativeLattice_sample_disjoint (ctx : RuntimeCtx kind) (m ell : Nat) :
    List.Disjoint (internalKeys ctx m ell) ctx.keys := by
  have unique := (context ctx m ell).keysNodup
  change (context ctx m ell).keys.Nodup at unique
  rw [nativeLattice_sample_keys] at unique
  apply List.disjoint_left.mpr
  intro key internal external
  exact (List.nodup_append.mp unique).2.2 key internal key external rfl

/-- Lifting a structural input through all four real fields preserves its exact key support. -/
theorem nativeLattice_sample_underRead_keys {shape : CShape}
    (input : CInputRef ctx shape) (m ell : Nat) :
    (underRead input m ell).storageKeys = input.storageKeys := by
  let first : CInputRef (context1 ctx m ell) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (ell + m)) ctx.canonicalFreshKey_fresh
  let second : CInputRef (context2 ctx m ell) shape :=
    first.underWorkspace (context1 ctx m ell).canonicalFreshKey (.unsignedWord ell)
      (context1 ctx m ell).canonicalFreshKey_fresh
  let third : CInputRef (context3 ctx m ell) shape :=
    second.underWorkspace (context2 ctx m ell).canonicalFreshKey (.unsignedWord (ell + m))
      (context2 ctx m ell).canonicalFreshKey_fresh
  exact (CInputRef.storageKeys_underWorkspace third (context3 ctx m ell).canonicalFreshKey
    (.unsignedWord ell) (context3 ctx m ell).canonicalFreshKey_fresh).trans
    ((CInputRef.storageKeys_underWorkspace second (context2 ctx m ell).canonicalFreshKey
      (.unsignedWord (ell + m)) (context2 ctx m ell).canonicalFreshKey_fresh).trans
      ((CInputRef.storageKeys_underWorkspace first (context1 ctx m ell).canonicalFreshKey
        (.unsignedWord ell) (context1 ctx m ell).canonicalFreshKey_fresh).trans
        (CInputRef.storageKeys_underWorkspace input ctx.canonicalFreshKey
          (.unsignedWord (ell + m)) ctx.canonicalFreshKey_fresh)))

/-- Actual entry preserves each original source, including both retained terminal values. -/
theorem nativeLattice_sample_push_read {shape : CShape}
    (input : CInputRef ctx shape) (m ell : Nat) (store : Store ctx) :
    (pushStore m ell store).read (underRead input m ell) = store.read input := by
  let firstRef : CInputRef (context1 ctx m ell) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (ell + m)) ctx.canonicalFreshKey_fresh
  let secondRef : CInputRef (context2 ctx m ell) shape :=
    firstRef.underWorkspace (context1 ctx m ell).canonicalFreshKey (.unsignedWord ell)
      (context1 ctx m ell).canonicalFreshKey_fresh
  let thirdRef : CInputRef (context3 ctx m ell) shape :=
    secondRef.underWorkspace (context2 ctx m ell).canonicalFreshKey (.unsignedWord (ell + m))
      (context2 ctx m ell).canonicalFreshKey_fresh
  let first : Store (context1 ctx m ell) :=
    store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (ell + m)) ctx.canonicalFreshKey_fresh
  let second : Store (context2 ctx m ell) :=
    first.pushWorkspace (context1 ctx m ell).canonicalFreshKey (.unsignedWord ell)
      (context1 ctx m ell).canonicalFreshKey_fresh
  let third : Store (context3 ctx m ell) :=
    second.pushWorkspace (context2 ctx m ell).canonicalFreshKey (.unsignedWord (ell + m))
      (context2 ctx m ell).canonicalFreshKey_fresh
  exact (Store.read_pushWorkspace_underWorkspace third (context3 ctx m ell).canonicalFreshKey
    (.unsignedWord ell) (context3 ctx m ell).canonicalFreshKey_fresh thirdRef).trans
    ((Store.read_pushWorkspace_underWorkspace second (context2 ctx m ell).canonicalFreshKey
      (.unsignedWord (ell + m)) (context2 ctx m ell).canonicalFreshKey_fresh secondRef).trans
      ((Store.read_pushWorkspace_underWorkspace first (context1 ctx m ell).canonicalFreshKey
        (.unsignedWord ell) (context1 ctx m ell).canonicalFreshKey_fresh firstRef).trans
        (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
          (.unsignedWord (ell + m)) ctx.canonicalFreshKey_fresh input)))

/-- Actual reverse release exposes the same corresponding read in the original context. -/
theorem nativeLattice_sample_pop_read {shape : CShape}
    (input : CInputRef ctx shape) (m ell : Nat) (store : Store (context ctx m ell)) :
    (popStore m ell store).read input = store.read (underRead input m ell) := by
  let firstRef : CInputRef (context1 ctx m ell) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (ell + m)) ctx.canonicalFreshKey_fresh
  let secondRef : CInputRef (context2 ctx m ell) shape :=
    firstRef.underWorkspace (context1 ctx m ell).canonicalFreshKey (.unsignedWord ell)
      (context1 ctx m ell).canonicalFreshKey_fresh
  let thirdRef : CInputRef (context3 ctx m ell) shape :=
    secondRef.underWorkspace (context2 ctx m ell).canonicalFreshKey (.unsignedWord (ell + m))
      (context2 ctx m ell).canonicalFreshKey_fresh
  let third : Store (context3 ctx m ell) :=
    Store.popWorkspace (context3 ctx m ell).canonicalFreshKey (.unsignedWord ell)
      (context3 ctx m ell).canonicalFreshKey_fresh store
  let second : Store (context2 ctx m ell) :=
    Store.popWorkspace (context2 ctx m ell).canonicalFreshKey (.unsignedWord (ell + m))
      (context2 ctx m ell).canonicalFreshKey_fresh third
  let first : Store (context1 ctx m ell) :=
    Store.popWorkspace (context1 ctx m ell).canonicalFreshKey (.unsignedWord ell)
      (context1 ctx m ell).canonicalFreshKey_fresh second
  exact (Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey
    (.unsignedWord (ell + m)) ctx.canonicalFreshKey_fresh first input).trans
    ((Store.read_popWorkspace_underWorkspace (context1 ctx m ell).canonicalFreshKey
      (.unsignedWord ell) (context1 ctx m ell).canonicalFreshKey_fresh second firstRef).trans
      ((Store.read_popWorkspace_underWorkspace (context2 ctx m ell).canonicalFreshKey
        (.unsignedWord (ell + m)) (context2 ctx m ell).canonicalFreshKey_fresh
        third secondRef).trans
        (Store.read_popWorkspace_underWorkspace (context3 ctx m ell).canonicalFreshKey
          (.unsignedWord ell) (context3 ctx m ell).canonicalFreshKey_fresh store thirdRef)))

private def cellKey (ctx : RuntimeCtx kind) (m ell : Nat) (index : Fin 4) : StorageKey :=
  (internalKeys ctx m ell).get ⟨index.val, by change index.val < 4; exact index.isLt⟩

private theorem cellKey_ne (ctx : RuntimeCtx kind) (m ell : Nat)
    (left right : Fin 4) (different : left ≠ right) :
    cellKey ctx m ell left ≠ cellKey ctx m ell right := by
  intro same
  have positions := (nativeLattice_sample_nodup ctx m ell).injective_get same
  exact different (Fin.ext (congrArg Fin.val positions))

private theorem original_free {shape : CShape} (input : CInputRef ctx shape)
    (m ell : Nat) (index : Fin 4) :
    cellKey ctx m ell index ∉ (underRead input m ell).storageKeys := by
  rw [nativeLattice_sample_underRead_keys]
  intro present
  exact List.disjoint_left.mp (nativeLattice_sample_disjoint ctx m ell)
    (List.get_mem (internalKeys ctx m ell) _)
    (input.storageKeys_subset_context present)

/-- The actual first decoder's two surviving outputs occupy different physical storage entries. -/
theorem nativeLattice_sample_first_separated (ctx : RuntimeCtx kind) (m ell : Nat) :
    (firstRefs ctx m ell).j.key ≠ (firstRefs ctx m ell).k.key :=
  cellKey_ne ctx m ell 3 2 (by decide)

/-- The actual second decoder's two surviving outputs occupy different storage entries. -/
theorem nativeLattice_sample_second_separated (ctx : RuntimeCtx kind) (m ell : Nat) :
    (secondRefs ctx m ell).j.key ≠ (secondRefs ctx m ell).k.key :=
  cellKey_ne ctx m ell 1 0 (by decide)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.SampleLayout
