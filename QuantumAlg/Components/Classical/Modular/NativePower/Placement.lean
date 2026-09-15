/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Multiply
import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Lexical placement of full-product modular multiplication

Only the product and division pair are newly allocated. Their identities are
the canonical fresh keys of their actual parent contexts. Every operand and
the final result are lifted existing references; both scratch cells are popped
by their matching workspace instructions after the remainder is materialized.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The first lexical cell holds the complete product. -/
@[reducible] def productCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh

/-- The second lexical cell holds the actual quotient and remainder. -/
@[reducible] def divisionCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (productCtx ctx width).addWorkspace (productCtx ctx width).canonicalFreshKey
    (divisionShape width) (productCtx ctx width).canonicalFreshKey_fresh

/-- Preserve a structural read through both actual lexical allocations. -/
def underMultiply {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    CInputRef (divisionCtx ctx width) shape :=
  (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh).underWorkspace (productCtx ctx width).canonicalFreshKey
      (divisionShape width) (productCtx ctx width).canonicalFreshKey_fresh

/-- The existing output remains the same writable cell under both scopes. -/
def writeUnderMultiply {shape : CShape} (output : CWriteRef ctx shape) (width : Nat) :
    CWriteRef (divisionCtx ctx width) shape :=
  (output.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh).underWorkspace (productCtx ctx width).canonicalFreshKey
      (divisionShape width) (productCtx ctx width).canonicalFreshKey_fresh

/-- Actual first scratch cell, lifted past the subsequently allocated division pair. -/
def productCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (divisionCtx ctx width) (.unsignedWord (width + width)) :=
  (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh).underWorkspace (productCtx ctx width).canonicalFreshKey
      (divisionShape width) (productCtx ctx width).canonicalFreshKey_fresh

/-- Actual final scratch head containing both total division outputs. -/
def divisionCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (divisionCtx ctx width) (divisionShape width) :=
  CWriteRef.workspaceHead (productCtx ctx width) (productCtx ctx width).canonicalFreshKey
    (divisionShape width) (productCtx ctx width).canonicalFreshKey_fresh

/-- The three closed operations placed on their real input, result and scratch cells. -/
def placedMultiply (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit (divisionCtx ctx width) (divisionCtx ctx width) :=
  multiplyBody (underMultiply left width) (underMultiply right width)
    (underMultiply modulus width) (productCell ctx width) (divisionCell ctx width)
    (writeUnderMultiply output width)

/-- Execute real full-product reduction between matching lexical allocations and releases. -/
def scopedMultiply (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh
    (.workspace (productCtx ctx width) (productCtx ctx width).canonicalFreshKey
      (divisionShape width) (productCtx ctx width).canonicalFreshKey_fresh
      (placedMultiply left right modulus output))

/-- Concrete contents after entering both actual scratch scopes. -/
def enterMultiply (store : Store ctx) (width : Nat) : Store (divisionCtx ctx width) :=
  (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh).pushWorkspace (productCtx ctx width).canonicalFreshKey
      (divisionShape width) (productCtx ctx width).canonicalFreshKey_fresh

/-- Release exactly the two scratch heads, preserving the existing outer store. -/
def leaveMultiply (store : Store (divisionCtx ctx width)) : Store ctx :=
  Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh
    (Store.popWorkspace (productCtx ctx width).canonicalFreshKey (divisionShape width)
      (productCtx ctx width).canonicalFreshKey_fresh store)

/-- The actual outer-store update, together with the program's real three-operation path. -/
def scopedMultiplyStep (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (scopedMultiply left right modulus output).Path :=
  (leaveMultiply
    (multiplyStore (underMultiply left width) (underMultiply right width)
      (underMultiply modulus width) (productCell ctx width) (divisionCell ctx width)
      (writeUnderMultiply output width) (enterMultiply store width)), ((), ((), ())))

end QuantumAlg.ClassicalRoutines.Modular.NativePower
