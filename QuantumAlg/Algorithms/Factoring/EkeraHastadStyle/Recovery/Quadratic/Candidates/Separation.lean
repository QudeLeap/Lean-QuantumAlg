/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Layout

/-!
# Intrinsic separation of the actual quadratic words

The concrete four-word layout proves the exact read-preservation conditions
needed by the candidate arithmetic. The source modulus remains an original
structural read. These conditions are discharged by allocation and never
become new assumptions about the caller's cells or state.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The four real destination identities written by the native candidate program. -/
def writeKeys (refs : Refs ctx width) : List StorageKey :=
  [refs.center.key, refs.root.key, refs.first.key, refs.second.key]

/-- Internal read-separation facts for the actual candidate instructions. -/
structure Separated (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Refs ctx width) : Prop where
  /-- All candidate writes preserve the original modulus. -/
  modulusFree : ∀ key ∈ writeKeys refs, key ∉ modulus.storageKeys
  /-- Squaring and square-root updates preserve the center. -/
  centerRoot : refs.center.key ≠ refs.root.key
  /-- The lower candidate does not overwrite its center operand. -/
  centerFirst : refs.center.key ≠ refs.first.key
  /-- The upper candidate also preserves the center. -/
  centerSecond : refs.center.key ≠ refs.second.key
  /-- The lower candidate preserves the computed square root. -/
  rootFirst : refs.root.key ≠ refs.first.key
  /-- The upper candidate preserves the computed square root. -/
  rootSecond : refs.root.key ≠ refs.second.key
  /-- Computing the upper candidate retains the lower candidate for the first check. -/
  firstSecond : refs.first.key ≠ refs.second.key

/-- The four real workspace lifts retain precisely the original structural key support. -/
lemma nativeQuadratic_underRead_keys {shape : CShape} (input : CInputRef ctx shape) :
    (Layout.underRead input width).storageKeys = input.storageKeys := by
  let first : CInputRef (Layout.centerCtx ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (RSA.quadraticWordWidth width))
      ctx.canonicalFreshKey_fresh
  let second : CInputRef (Layout.rootCtx ctx width) shape :=
    first.underWorkspace (Layout.centerCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width))
      (Layout.centerCtx ctx width).canonicalFreshKey_fresh
  let third : CInputRef (Layout.firstCtx ctx width) shape :=
    second.underWorkspace (Layout.rootCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width))
      (Layout.rootCtx ctx width).canonicalFreshKey_fresh
  exact (CInputRef.storageKeys_underWorkspace third
    (Layout.firstCtx ctx width).canonicalFreshKey (.unsignedWord (RSA.quadraticWordWidth width))
    (Layout.firstCtx ctx width).canonicalFreshKey_fresh).trans
    ((CInputRef.storageKeys_underWorkspace second
      (Layout.rootCtx ctx width).canonicalFreshKey (.unsignedWord (RSA.quadraticWordWidth width))
      (Layout.rootCtx ctx width).canonicalFreshKey_fresh).trans
      ((CInputRef.storageKeys_underWorkspace first
        (Layout.centerCtx ctx width).canonicalFreshKey
        (.unsignedWord (RSA.quadraticWordWidth width))
        (Layout.centerCtx ctx width).canonicalFreshKey_fresh).trans
        (CInputRef.storageKeys_underWorkspace input ctx.canonicalFreshKey
          (.unsignedWord (RSA.quadraticWordWidth width)) ctx.canonicalFreshKey_fresh)))

/-- Every actual candidate word is outside every original structural read. -/
lemma nativeQuadratic_underRead_free {shape : CShape} (input : CInputRef ctx shape)
    (key : StorageKey) (present : key ∈ Layout.internalKeys ctx width) :
    key ∉ (Layout.underRead input width).storageKeys := by
  rw [nativeQuadratic_underRead_keys]
  intro member
  exact List.disjoint_left.mp (Layout.nativeQuadratic_layout_disjoint ctx width)
    present (input.storageKeys_subset_context member)

private def cellKey (ctx : RuntimeCtx kind) (width : Nat) (index : Fin 4) : StorageKey :=
  (Layout.internalKeys ctx width).get ⟨index.val, by change index.val < 4; exact index.isLt⟩

private lemma cellKey_ne (ctx : RuntimeCtx kind) (width : Nat)
    (left right : Fin 4) (different : left ≠ right) :
    cellKey ctx width left ≠ cellKey ctx width right := by
  intro same
  have positions := (Layout.nativeQuadratic_layout_nodup ctx width).injective_get same
  exact different (Fin.ext (congrArg Fin.val positions))

/-- Actual allocation discharges every arithmetic separation condition internally. -/
lemma nativeQuadratic_layout_separated
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width))) :
    Separated (Layout.underRead modulus width) (Layout.refs ctx width) where
  modulusFree := by
    intro key present
    change key ∈ [(Layout.center ctx width).key, (Layout.root ctx width).key,
      (Layout.first ctx width).key, (Layout.second ctx width).key] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl | rfl
    all_goals exact nativeQuadratic_underRead_free modulus _ (by simp [Layout.internalKeys])
  centerRoot := cellKey_ne ctx width 3 2 (by decide)
  centerFirst := cellKey_ne ctx width 3 1 (by decide)
  centerSecond := cellKey_ne ctx width 3 0 (by decide)
  rootFirst := cellKey_ne ctx width 2 1 (by decide)
  rootSecond := cellKey_ne ctx width 2 0 (by decide)
  firstSecond := cellKey_ne ctx width 1 0 (by decide)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
