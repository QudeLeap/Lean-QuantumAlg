/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Operations

/-!
# Four actual lexical words for quadratic candidates

The center, reused discriminant/root and two candidate words occupy four
distinct freshly allocated classical cells. Their keys lie outside all
original source reads and selector storage. The scopes retain the original
quantum bank unchanged; candidate validation takes place in the inner body
before these same four words are released.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Layout

variable {kind : ProblemKind}

/-- First actual lexical word stores the source center. -/
def centerCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord (RSA.quadraticWordWidth width))
    ctx.canonicalFreshKey_fresh

/-- Second actual word is reused from the center square through the computed square root. -/
def rootCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (centerCtx ctx width).addWorkspace (centerCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width)) (centerCtx ctx width).canonicalFreshKey_fresh

/-- Third actual word holds the lower source candidate. -/
def firstCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (rootCtx ctx width).addWorkspace (rootCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width)) (rootCtx ctx width).canonicalFreshKey_fresh

/-- Fourth actual word holds the independently checked upper source candidate. -/
def context (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (firstCtx ctx width).addWorkspace (firstCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width)) (firstCtx ctx width).canonicalFreshKey_fresh

/-- The actual center cell beneath the three subsequent workspace words. -/
def center (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord (RSA.quadraticWordWidth width)) where
  key := ctx.canonicalFreshKey
  role := .workspace
  slot := .there (.there (.there .here))
  writable := by decide

/-- The actual reused square-root cell beneath the two candidate words. -/
def root (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord (RSA.quadraticWordWidth width)) where
  key := (centerCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .there (.there .here)
  writable := by decide

/-- The actual lower-candidate cell immediately below the upper-candidate head. -/
def first (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord (RSA.quadraticWordWidth width)) where
  key := (rootCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .there .here
  writable := by decide

/-- The actual upper-candidate workspace head. -/
def second (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord (RSA.quadraticWordWidth width)) where
  key := (firstCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .here
  writable := by decide

/-- The native candidate program receives exactly these four intrinsically placed cells. -/
def refs (ctx : RuntimeCtx kind) (width : Nat) : Refs (context ctx width) width where
  center := center ctx width
  root := root ctx width
  first := first ctx width
  second := second ctx width

/-- Original structural inputs keep the same stored values beneath the four real words. -/
def underRead {ctx : RuntimeCtx kind} {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) : CInputRef (context ctx width) shape :=
  let first := input.underWorkspace ctx.canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width)) ctx.canonicalFreshKey_fresh
  let second := first.underWorkspace (centerCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width)) (centerCtx ctx width).canonicalFreshKey_fresh
  let third := second.underWorkspace (rootCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width)) (rootCtx ctx width).canonicalFreshKey_fresh
  third.underWorkspace (firstCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width)) (firstCtx ctx width).canonicalFreshKey_fresh

/-- Original writable selector cells remain the same physical slots below the candidate words. -/
def underWrite {ctx : RuntimeCtx kind} {shape : CShape} (output : CWriteRef ctx shape)
    (width : Nat) : CWriteRef (context ctx width) shape :=
  let first := output.underWorkspace ctx.canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width)) ctx.canonicalFreshKey_fresh
  let second := first.underWorkspace (centerCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width)) (centerCtx ctx width).canonicalFreshKey_fresh
  let third := second.underWorkspace (rootCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width)) (rootCtx ctx width).canonicalFreshKey_fresh
  third.underWorkspace (firstCtx ctx width).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width)) (firstCtx ctx width).canonicalFreshKey_fresh

/-- Intrinsic keys of the four candidate cells, in their actual newest-first context order. -/
def internalKeys (ctx : RuntimeCtx kind) (width : Nat) : List StorageKey :=
  [(second ctx width).key, (first ctx width).key, (root ctx width).key, (center ctx width).key]

/-- The actual context contains precisely these four fresh words and the old entries. -/
theorem nativeQuadratic_layout_keys (ctx : RuntimeCtx kind) (width : Nat) :
    (context ctx width).keys = internalKeys ctx width ++ ctx.keys := rfl

/-- Actual runtime key uniqueness proves that every candidate word is distinct. -/
theorem nativeQuadratic_layout_nodup (ctx : RuntimeCtx kind) (width : Nat) :
    (internalKeys ctx width).Nodup := by
  have unique := (context ctx width).keysNodup
  change (context ctx width).keys.Nodup at unique
  rw [nativeQuadratic_layout_keys] at unique
  exact (List.nodup_append.mp unique).1

/-- No original source or selector cell overlaps any actual candidate workspace. -/
theorem nativeQuadratic_layout_disjoint (ctx : RuntimeCtx kind) (width : Nat) :
    List.Disjoint (internalKeys ctx width) ctx.keys := by
  have unique := (context ctx width).keysNodup
  change (context ctx width).keys.Nodup at unique
  rw [nativeQuadratic_layout_keys] at unique
  apply List.disjoint_left.mpr
  intro key internal external
  exact (List.nodup_append.mp unique).2.2 key internal key external rfl

/-- All four allocations are classical and retain the caller's exact quantum bank. -/
theorem nativeQuadratic_layout_quantumWires (ctx : RuntimeCtx kind) (width : Nat) :
    (context ctx width).quantumWires = ctx.quantumWires := rfl

/-- The real four-word scope encloses candidate calculation and both actual divisor checks. -/
def scopes {model : ExecutionModel} (ctx : RuntimeCtx model.kind) (width : Nat)
    (inner : Circuit model (context ctx width) (context ctx width)) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord (RSA.quadraticWordWidth width))
    ctx.canonicalFreshKey_fresh
    (.workspace (centerCtx ctx width) (centerCtx ctx width).canonicalFreshKey
      (.unsignedWord (RSA.quadraticWordWidth width)) (centerCtx ctx width).canonicalFreshKey_fresh
      (.workspace (rootCtx ctx width) (rootCtx ctx width).canonicalFreshKey
        (.unsignedWord (RSA.quadraticWordWidth width)) (rootCtx ctx width).canonicalFreshKey_fresh
        (.workspace (firstCtx ctx width) (firstCtx ctx width).canonicalFreshKey
          (.unsignedWord (RSA.quadraticWordWidth width))
          (firstCtx ctx width).canonicalFreshKey_fresh inner)))

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Layout
