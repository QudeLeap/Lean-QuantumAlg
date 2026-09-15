/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Basis.FirstRow

/-!
# Three actual lexical coordinates of a lattice row

The row consists of three separately writable native words, allocated in
coordinate order and released in reverse. The same row layout is used for
each of the three basis rows and for the three-coordinate target. No packed
basis or target is introduced as a runtime instruction. Original sample and
persistent result references retain their intrinsic storage positions.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.RowLayout

open Execution

variable {kind : ProblemKind}

private def context1 (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh

private def context2 (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (context1 ctx width).addWorkspace (context1 ctx width).canonicalFreshKey (.unsignedWord width)
    (context1 ctx width).canonicalFreshKey_fresh

/-- Three actual lexical word cells hold one row, with no additional quantum system. -/
def context (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (context2 ctx width).addWorkspace (context2 ctx width).canonicalFreshKey (.unsignedWord width)
    (context2 ctx width).canonicalFreshKey_fresh

/-- Original structural reads keep their positions below all three real row cells. -/
def underRead {ctx : RuntimeCtx kind} {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) : CInputRef (context ctx width) shape :=
  ((input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace
      (context1 ctx width).canonicalFreshKey (.unsignedWord width)
      (context1 ctx width).canonicalFreshKey_fresh).underWorkspace
      (context2 ctx width).canonicalFreshKey (.unsignedWord width)
      (context2 ctx width).canonicalFreshKey_fresh

/-- Original writable cells remain the same actual cells under the three row coordinates. -/
def underWrite {ctx : RuntimeCtx kind} {shape : CShape} (output : CWriteRef ctx shape)
    (width : Nat) : CWriteRef (context ctx width) shape :=
  ((output.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace
      (context1 ctx width).canonicalFreshKey (.unsignedWord width)
      (context1 ctx width).canonicalFreshKey_fresh).underWorkspace
      (context2 ctx width).canonicalFreshKey (.unsignedWord width)
      (context2 ctx width).canonicalFreshKey_fresh

/-- The three intrinsic destinations are exactly the three actual newly allocated words. -/
def refs (ctx : RuntimeCtx kind) (width : Nat) : FirstRow.Refs (context ctx width) width where
  first := ((CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace
      (context1 ctx width).canonicalFreshKey (.unsignedWord width)
      (context1 ctx width).canonicalFreshKey_fresh).underWorkspace
      (context2 ctx width).canonicalFreshKey (.unsignedWord width)
      (context2 ctx width).canonicalFreshKey_fresh
  second := (CWriteRef.workspaceHead (context1 ctx width)
    (context1 ctx width).canonicalFreshKey (.unsignedWord width)
    (context1 ctx width).canonicalFreshKey_fresh).underWorkspace
      (context2 ctx width).canonicalFreshKey (.unsignedWord width)
      (context2 ctx width).canonicalFreshKey_fresh
  third := CWriteRef.workspaceHead (context2 ctx width)
    (context2 ctx width).canonicalFreshKey (.unsignedWord width)
    (context2 ctx width).canonicalFreshKey_fresh

/-- Entry supplies the same three actual zero-initialized row cells in coordinate order. -/
def pushStore {ctx : RuntimeCtx kind} (width : Nat) (store : Store ctx) :
    Store (context ctx width) :=
  ((store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).pushWorkspace
      (context1 ctx width).canonicalFreshKey (.unsignedWord width)
      (context1 ctx width).canonicalFreshKey_fresh).pushWorkspace
      (context2 ctx width).canonicalFreshKey (.unsignedWord width)
      (context2 ctx width).canonicalFreshKey_fresh

/-- Reverse release removes exactly these row cells after their actual computation. -/
def popStore {ctx : RuntimeCtx kind} (width : Nat) (store : Store (context ctx width)) :
    Store ctx :=
  Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (Store.popWorkspace (context1 ctx width).canonicalFreshKey (.unsignedWord width)
      (context1 ctx width).canonicalFreshKey_fresh
      (Store.popWorkspace (context2 ctx width).canonicalFreshKey (.unsignedWord width)
        (context2 ctx width).canonicalFreshKey_fresh store))

/-- Three real lexical constructors supply, use and release the actual row coordinates. -/
def scopes (ctx : RuntimeCtx kind) (width : Nat)
    (body : Circuit (context ctx width) (context ctx width)) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (.workspace (context1 ctx width) (context1 ctx width).canonicalFreshKey (.unsignedWord width)
      (context1 ctx width).canonicalFreshKey_fresh
      (.workspace (context2 ctx width) (context2 ctx width).canonicalFreshKey (.unsignedWord width)
        (context2 ctx width).canonicalFreshKey_fresh body))

/-- The complete original quantum bank retains its actual wire identities and dimensions. -/
theorem nativeLattice_row_quantumWires (ctx : RuntimeCtx kind) (width : Nat) :
    (context ctx width).quantumWires = ctx.quantumWires := rfl

/-- The real row scope keeps the body's exact execution path, with no invented events. -/
theorem nativeLattice_row_scope_trace (ctx : RuntimeCtx kind) (width : Nat)
    (body : Circuit (context ctx width) (context ctx width))
    (path : (scopes ctx width body).Path) :
    (scopes ctx width body).eventTrace path = body.eventTrace path := rfl

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.RowLayout
