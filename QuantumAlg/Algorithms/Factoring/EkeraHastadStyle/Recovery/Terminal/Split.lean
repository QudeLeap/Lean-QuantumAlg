/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Terminal
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Terminal.Shift

/-!
# Actual terminal decoding and source sample split

The original terminal bits are decoded into one real fresh full-index word.
The low word is resized into k before ell actual right shifts reuse that
same full-index word. A final resize writes j. The full-index word is then
released by its enclosing scope. The stored outputs are the source's high
quotient and low remainder; neither output requires an initial value.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.TerminalSplit

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {m ell : Nat}

/-- Actual writable destinations for the two original source sample fields. -/
structure Refs (ctx : RuntimeCtx kind) (m ell : Nat) where
  /-- The high exponent-register index. -/
  j : CWriteRef ctx (.unsignedWord (ell + m))
  /-- The low exponent-register index. -/
  k : CWriteRef ctx (.unsignedWord ell)

/-- One actual lexical word stores and then shifts the decoded full terminal index. -/
def context (ctx : RuntimeCtx kind) (m ell : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord ((ell + m) + ell))
    ctx.canonicalFreshKey_fresh

/-- The intrinsic actual full-index word at the newly allocated head. -/
def full (ctx : RuntimeCtx kind) (m ell : Nat) :
    CWriteRef (context ctx m ell) (.unsignedWord ((ell + m) + ell)) :=
  .workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord ((ell + m) + ell))
    ctx.canonicalFreshKey_fresh

/-- Original inputs keep their intrinsic references under the one real full-index word. -/
def underRead {shape : CShape} (input : CInputRef ctx shape) (m ell : Nat) :
    CInputRef (context ctx m ell) shape :=
  input.underWorkspace ctx.canonicalFreshKey (.unsignedWord ((ell + m) + ell))
    ctx.canonicalFreshKey_fresh

/-- Low-word extraction is the original real resize before the full word is shifted. -/
def lowOp (refs : Refs ctx m ell) :
    ClassicalOp (.unsignedWord ((ell + m) + ell)) (.unsignedWord ell)
      (context ctx m ell) (context ctx m ell) :=
  .wordResize ((ell + m) + ell) ell (context ctx m ell)
    (.storage (full ctx m ell).toCStorageRef)
    (refs.k.underWorkspace ctx.canonicalFreshKey (.unsignedWord ((ell + m) + ell))
      ctx.canonicalFreshKey_fresh)

/-- High-word extraction resizes the same actual full word after its real ell shifts. -/
def highOp (refs : Refs ctx m ell) :
    ClassicalOp (.unsignedWord ((ell + m) + ell)) (.unsignedWord (ell + m))
      (context ctx m ell) (context ctx m ell) :=
  .wordResize ((ell + m) + ell) (ell + m) (context ctx m ell)
    (.storage (full ctx m ell).toCStorageRef)
    (refs.j.underWorkspace ctx.canonicalFreshKey (.unsignedWord ((ell + m) + ell))
      ctx.canonicalFreshKey_fresh)

/-- Actual decoding, low extraction, repeated shifts and high extraction, in source order. -/
def body (input : CInputRef ctx (.bits ((ell + m) + ell))) (refs : Refs ctx m ell) :
    Circuit (context ctx m ell) (context ctx m ell) :=
  .seq (terminalCircuit (underRead input m ell) (full ctx m ell))
    (.seq (.classical (lowOp refs))
      (.seq (TerminalShift.code ell (full ctx m ell)) (.classical (highOp refs))))

/-- The actual decoder supplies and releases its only internal full-index word. -/
def code (input : CInputRef ctx (.bits ((ell + m) + ell))) (refs : Refs ctx m ell) :
    Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord ((ell + m) + ell))
    ctx.canonicalFreshKey_fresh (body input refs)

noncomputable section

/-- The recorded store and path follow the actual decoder and both extraction instructions. -/
def bodyStep (input : CInputRef ctx (.bits ((ell + m) + ell))) (refs : Refs ctx m ell)
    (store : Store (context ctx m ell)) :
    Store (context ctx m ell) × (body input refs).Path :=
  let decoded := terminalStep (underRead input m ell) (full ctx m ell) store
  let low := decoded.1.applyOp (lowOp refs)
  let shifted := TerminalShift.storeStep ell (full ctx m ell) low
  (shifted.applyOp (highOp refs), (decoded.2, ((), ((fun _ : Fin ell => ()), ()))))

/-- Actual allocation and reverse release leave only the two original writable output fields. -/
def step (input : CInputRef ctx (.bits ((ell + m) + ell))) (refs : Refs ctx m ell)
    (store : Store ctx) : Store ctx × (code input refs).Path :=
  let result := bodyStep input refs
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord ((ell + m) + ell))
      ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord ((ell + m) + ell))
    ctx.canonicalFreshKey_fresh result.1, result.2)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.TerminalSplit
