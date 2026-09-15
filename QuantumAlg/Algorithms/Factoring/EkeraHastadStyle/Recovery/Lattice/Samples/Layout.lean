/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Terminal.Split

/-!
# Actual four-word layout for a pair of decoded source samples

Four lexical cells hold the two original j/k pairs. The two decoders run
sequentially inside this layout; each separately supplies and releases its
one full-index temporary. Every original structural input remains available
under the four real cells, and reverse release returns the original context.
No initialization condition is needed for the sample destinations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.SampleLayout

open Execution

variable {kind : ProblemKind}

private def context1 (ctx : RuntimeCtx kind) (m ell : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord (ell + m)) ctx.canonicalFreshKey_fresh

private def context2 (ctx : RuntimeCtx kind) (m ell : Nat) : RuntimeCtx kind :=
  (context1 ctx m ell).addWorkspace (context1 ctx m ell).canonicalFreshKey
    (.unsignedWord ell) (context1 ctx m ell).canonicalFreshKey_fresh

private def context3 (ctx : RuntimeCtx kind) (m ell : Nat) : RuntimeCtx kind :=
  (context2 ctx m ell).addWorkspace (context2 ctx m ell).canonicalFreshKey
    (.unsignedWord (ell + m)) (context2 ctx m ell).canonicalFreshKey_fresh

/-- Four actual independently writable words store the original two sample pairs. -/
def context (ctx : RuntimeCtx kind) (m ell : Nat) : RuntimeCtx kind :=
  (context3 ctx m ell).addWorkspace (context3 ctx m ell).canonicalFreshKey
    (.unsignedWord ell) (context3 ctx m ell).canonicalFreshKey_fresh

/-- Intrinsic destinations of the first terminal, lifted under the other three sample fields. -/
def firstRefs (ctx : RuntimeCtx kind) (m ell : Nat) :
    TerminalSplit.Refs (context ctx m ell) m ell where
  j := (((CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord (ell + m))
    ctx.canonicalFreshKey_fresh).underWorkspace
      (context1 ctx m ell).canonicalFreshKey (.unsignedWord ell)
      (context1 ctx m ell).canonicalFreshKey_fresh).underWorkspace
      (context2 ctx m ell).canonicalFreshKey (.unsignedWord (ell + m))
      (context2 ctx m ell).canonicalFreshKey_fresh).underWorkspace
      (context3 ctx m ell).canonicalFreshKey (.unsignedWord ell)
      (context3 ctx m ell).canonicalFreshKey_fresh
  k := ((CWriteRef.workspaceHead (context1 ctx m ell)
    (context1 ctx m ell).canonicalFreshKey (.unsignedWord ell)
    (context1 ctx m ell).canonicalFreshKey_fresh).underWorkspace
      (context2 ctx m ell).canonicalFreshKey (.unsignedWord (ell + m))
      (context2 ctx m ell).canonicalFreshKey_fresh).underWorkspace
      (context3 ctx m ell).canonicalFreshKey (.unsignedWord ell)
      (context3 ctx m ell).canonicalFreshKey_fresh

/-- Intrinsic destinations of the second terminal are the last two actual sample cells. -/
def secondRefs (ctx : RuntimeCtx kind) (m ell : Nat) :
    TerminalSplit.Refs (context ctx m ell) m ell where
  j := (CWriteRef.workspaceHead (context2 ctx m ell)
    (context2 ctx m ell).canonicalFreshKey (.unsignedWord (ell + m))
    (context2 ctx m ell).canonicalFreshKey_fresh).underWorkspace
      (context3 ctx m ell).canonicalFreshKey (.unsignedWord ell)
      (context3 ctx m ell).canonicalFreshKey_fresh
  k := CWriteRef.workspaceHead (context3 ctx m ell)
    (context3 ctx m ell).canonicalFreshKey (.unsignedWord ell)
    (context3 ctx m ell).canonicalFreshKey_fresh

/-- Every existing structural source remains readable beneath the four actual sample words. -/
def underRead {ctx : RuntimeCtx kind} {shape : CShape}
    (input : CInputRef ctx shape) (m ell : Nat) : CInputRef (context ctx m ell) shape :=
  (((input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (ell + m))
    ctx.canonicalFreshKey_fresh).underWorkspace
      (context1 ctx m ell).canonicalFreshKey (.unsignedWord ell)
      (context1 ctx m ell).canonicalFreshKey_fresh).underWorkspace
      (context2 ctx m ell).canonicalFreshKey (.unsignedWord (ell + m))
      (context2 ctx m ell).canonicalFreshKey_fresh).underWorkspace
      (context3 ctx m ell).canonicalFreshKey (.unsignedWord ell)
      (context3 ctx m ell).canonicalFreshKey_fresh

/-- Actual entry supplies the four sample cells in their chronological allocation order. -/
def pushStore {ctx : RuntimeCtx kind} (m ell : Nat) (store : Store ctx) :
    Store (context ctx m ell) :=
  (((store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (ell + m))
    ctx.canonicalFreshKey_fresh).pushWorkspace
      (context1 ctx m ell).canonicalFreshKey (.unsignedWord ell)
      (context1 ctx m ell).canonicalFreshKey_fresh).pushWorkspace
      (context2 ctx m ell).canonicalFreshKey (.unsignedWord (ell + m))
      (context2 ctx m ell).canonicalFreshKey_fresh).pushWorkspace
      (context3 ctx m ell).canonicalFreshKey (.unsignedWord ell)
      (context3 ctx m ell).canonicalFreshKey_fresh

/-- Reverse lexical release exposes the same original store after the actual pair computation. -/
def popStore {ctx : RuntimeCtx kind} (m ell : Nat) (store : Store (context ctx m ell)) :
    Store ctx :=
  Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (ell + m)) ctx.canonicalFreshKey_fresh
    (Store.popWorkspace (context1 ctx m ell).canonicalFreshKey (.unsignedWord ell)
      (context1 ctx m ell).canonicalFreshKey_fresh
      (Store.popWorkspace (context2 ctx m ell).canonicalFreshKey (.unsignedWord (ell + m))
        (context2 ctx m ell).canonicalFreshKey_fresh
        (Store.popWorkspace (context3 ctx m ell).canonicalFreshKey (.unsignedWord ell)
          (context3 ctx m ell).canonicalFreshKey_fresh store)))

/-- Actual lexical constructors supply, execute with and release these four sample fields. -/
def scopes (ctx : RuntimeCtx kind) (m ell : Nat)
    (body : Circuit (context ctx m ell) (context ctx m ell)) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord (ell + m)) ctx.canonicalFreshKey_fresh
    (.workspace (context1 ctx m ell) (context1 ctx m ell).canonicalFreshKey (.unsignedWord ell)
      (context1 ctx m ell).canonicalFreshKey_fresh
      (.workspace (context2 ctx m ell) (context2 ctx m ell).canonicalFreshKey
        (.unsignedWord (ell + m)) (context2 ctx m ell).canonicalFreshKey_fresh
        (.workspace (context3 ctx m ell) (context3 ctx m ell).canonicalFreshKey (.unsignedWord ell)
          (context3 ctx m ell).canonicalFreshKey_fresh body)))

/-- The pair prefix decodes the original first terminal before the original second terminal. -/
def decode {ctx : RuntimeCtx kind} {m ell : Nat}
    (first second : CInputRef ctx (.bits ((ell + m) + ell))) :
    Circuit (context ctx m ell) (context ctx m ell) :=
  .seq (TerminalSplit.code (underRead first m ell) (firstRefs ctx m ell))
    (TerminalSplit.code (underRead second m ell) (secondRefs ctx m ell))

noncomputable section

/-- The recorded prefix update is the same ordered pair of actual decoder steps. -/
def decodeStep {ctx : RuntimeCtx kind} {m ell : Nat}
    (first second : CInputRef ctx (.bits ((ell + m) + ell)))
    (store : Store (context ctx m ell)) : Store (context ctx m ell) × (decode first second).Path :=
  let firstResult := TerminalSplit.step (underRead first m ell) (firstRefs ctx m ell) store
  let secondResult :=
    TerminalSplit.step (underRead second m ell) (secondRefs ctx m ell) firstResult.1
  (secondResult.1, (firstResult.2, secondResult.2))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.SampleLayout
