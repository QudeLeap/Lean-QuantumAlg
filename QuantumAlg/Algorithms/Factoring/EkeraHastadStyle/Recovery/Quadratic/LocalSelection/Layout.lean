/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Selection.Scope
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check.Wiring

/-!
# Actual local candidate selection beneath the persistent result

The existing selection layout supplies one wide local candidate latch and
three Boolean cells. Four real candidate words and the five existing checker
cells are nested inside that scope. The caller's result latches remain their
original writable cells throughout. Both local checks and local selection
finish before the separate actual narrowing operation can update that result.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.LocalLayout

open ClassicalRoutines

variable {kind : ProblemKind}

/-- The existing four-cell selector layout is reused for the local wide candidate result. -/
def selectionContext (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  SelectionLayout.context ctx (RSA.quadraticWordWidth width)

/-- The four actual candidate words are inside the real local selection scope. -/
def candidateContext (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  Layout.context (selectionContext ctx width) width

/-- Both checks and the final conversion run inside the same actual checker cells. -/
def context (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  CheckLayout.context (candidateContext ctx width) (RSA.quadraticWordWidth width)

/-- Old writable cells keep their intrinsic positions beneath the four local selector entries. -/
def selectionUnderWrite {ctx : RuntimeCtx kind} {shape : CShape}
    (output : CWriteRef ctx shape) (width : Nat) : CWriteRef (selectionContext ctx width) shape :=
  let first := output.underWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
  let second := first.underWorkspace (SelectionLayout.acceptedCtx ctx).canonicalFreshKey
    (.unsignedWord (RSA.quadraticWordWidth width))
    (SelectionLayout.acceptedCtx ctx).canonicalFreshKey_fresh
  let third := second.underWorkspace
    (SelectionLayout.selectedCtx ctx (RSA.quadraticWordWidth width)).canonicalFreshKey .bit
    (SelectionLayout.selectedCtx ctx (RSA.quadraticWordWidth width)).canonicalFreshKey_fresh
  third.underWorkspace
    (SelectionLayout.availableCtx ctx (RSA.quadraticWordWidth width)).canonicalFreshKey .bit
    (SelectionLayout.availableCtx ctx (RSA.quadraticWordWidth width)).canonicalFreshKey_fresh

/-- The candidate calculation reads the original structural source beneath the two outer scopes.
-/
def arithmeticRead {ctx : RuntimeCtx kind} {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) : CInputRef (candidateContext ctx width) shape :=
  Layout.underRead (SelectionLayout.underRead input (RSA.quadraticWordWidth width)) width

/-- The native arithmetic uses exactly the four existing candidate-layout destinations. -/
def arithmeticRefs (ctx : RuntimeCtx kind) (width : Nat) :
    Refs (candidateContext ctx width) width :=
  Layout.refs (selectionContext ctx width) width

/-- The same local selector cells receive the checked candidates beneath the four real words. -/
def localRefs (ctx : RuntimeCtx kind) (width : Nat) :
    FirstAccepted.Refs (candidateContext ctx width) (RSA.quadraticWordWidth width) where
  accepted := Layout.underWrite
    (SelectionLayout.accepted ctx (RSA.quadraticWordWidth width)) width
  selected := Layout.underWrite
    (SelectionLayout.selected ctx (RSA.quadraticWordWidth width)) width
  available := Layout.underWrite
    (SelectionLayout.available ctx (RSA.quadraticWordWidth width)) width
  take := Layout.underWrite (SelectionLayout.take ctx (RSA.quadraticWordWidth width)) width

/-- The actual initialized one, reused remainder and two candidate words feed both checks. -/
def operands {ctx : RuntimeCtx kind} {width : Nat}
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width))) :
    CheckLayout.Operands (candidateContext ctx width) (RSA.quadraticWordWidth width) :=
  checkedOperands (arithmeticRead modulus width) (arithmeticRefs ctx width) (localRefs ctx width)

/-- The full two-check and local first-accepted interface uses the same actual inner positions. -/
def pairRefs {ctx : RuntimeCtx kind} {width : Nat}
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width))) :
    Pair.Refs (context ctx width) (RSA.quadraticWordWidth width) :=
  CheckLayout.pairRefs (operands modulus)

/-- An old writable result cell is lifted through precisely the existing three scope groups. -/
def underWrite {ctx : RuntimeCtx kind} {shape : CShape} (output : CWriteRef ctx shape)
    (width : Nat) : CWriteRef (context ctx width) shape :=
  CheckLayout.underWrite (Layout.underWrite (selectionUnderWrite output width) width)
    (RSA.quadraticWordWidth width)

/-- Persistent caller latches are not replaced by the local wide candidate result. -/
def persistentRefs {ctx : RuntimeCtx kind} {resultWidth : Nat}
    (original : FirstAccepted.Refs ctx resultWidth) (width : Nat) :
    FirstAccepted.Refs (context ctx width) resultWidth where
  accepted := underWrite original.accepted width
  selected := underWrite original.selected width
  available := underWrite original.available width
  take := underWrite original.take width

/-- Structural lifting retains each actual persistent storage identity. -/
theorem nativeQuadratic_local_underWrite_key {ctx : RuntimeCtx kind} {shape : CShape}
    (output : CWriteRef ctx shape) (width : Nat) :
    (underWrite output width).key = output.key := rfl

/-- All thirteen local cells are classical; the same original quantum bank remains in place. -/
theorem nativeQuadratic_local_quantumWires (ctx : RuntimeCtx kind) (width : Nat) :
    (context ctx width).quantumWires = ctx.quantumWires := rfl

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.LocalLayout
