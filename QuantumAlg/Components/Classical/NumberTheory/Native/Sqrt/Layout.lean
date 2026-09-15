/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Round

/-!
# Actual lexical layout of the native square root

Six real workspace heads hold the widened input, root, binary increment,
candidate, full square and comparison bit. Every key comes from the actual
preceding context. All original structural reads and writes are lifted
through those same heads. The complete scope adds no quantum system.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Fresh actual workspace for the widened original input. -/
@[reducible] def wideContext (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh

/-- Fresh actual workspace for the initial lower estimate. -/
@[reducible] def rootContext (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (wideContext ctx width).addWorkspace
    (wideContext ctx width).canonicalFreshKey (.unsignedWord width)
    (wideContext ctx width).canonicalFreshKey_fresh

/-- Fresh actual workspace for the binary increment. -/
@[reducible] def halfContext (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (rootContext ctx width).addWorkspace
    (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
    (rootContext ctx width).canonicalFreshKey_fresh

/-- Fresh actual workspace for the candidate midpoint. -/
@[reducible] def candidateContext (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (halfContext ctx width).addWorkspace
    (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
    (halfContext ctx width).canonicalFreshKey_fresh

/-- Fresh actual workspace for the full candidate square. -/
@[reducible] def squareContext (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (candidateContext ctx width).addWorkspace
    (candidateContext ctx width).canonicalFreshKey (.unsignedWord (width + width))
    (candidateContext ctx width).canonicalFreshKey_fresh

/-- Fresh actual workspace for the strict-comparison decision. -/
@[reducible] def context (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (squareContext ctx width).addWorkspace (squareContext ctx width).canonicalFreshKey .bit
    (squareContext ctx width).canonicalFreshKey_fresh

/-- Lift one original structured read through all six real scratch heads. -/
def underRead {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    CInputRef (context ctx width) shape :=
  let under1 := input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh
  let under2 := under1.underWorkspace
    (wideContext ctx width).canonicalFreshKey (.unsignedWord width)
    (wideContext ctx width).canonicalFreshKey_fresh
  let under3 := under2.underWorkspace
    (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
    (rootContext ctx width).canonicalFreshKey_fresh
  let under4 := under3.underWorkspace
    (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
    (halfContext ctx width).canonicalFreshKey_fresh
  let under5 := under4.underWorkspace
    (candidateContext ctx width).canonicalFreshKey (.unsignedWord (width + width))
    (candidateContext ctx width).canonicalFreshKey_fresh
  let under6 := under5.underWorkspace (squareContext ctx width).canonicalFreshKey .bit
    (squareContext ctx width).canonicalFreshKey_fresh
  under6

/-- Lift the actual caller destination through the same six scratch heads. -/
def underWrite {shape : CShape} (output : CWriteRef ctx shape) (width : Nat) :
    CWriteRef (context ctx width) shape :=
  let under1 := output.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh
  let under2 := under1.underWorkspace
    (wideContext ctx width).canonicalFreshKey (.unsignedWord width)
    (wideContext ctx width).canonicalFreshKey_fresh
  let under3 := under2.underWorkspace
    (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
    (rootContext ctx width).canonicalFreshKey_fresh
  let under4 := under3.underWorkspace
    (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
    (halfContext ctx width).canonicalFreshKey_fresh
  let under5 := under4.underWorkspace
    (candidateContext ctx width).canonicalFreshKey (.unsignedWord (width + width))
    (candidateContext ctx width).canonicalFreshKey_fresh
  let under6 := under5.underWorkspace (squareContext ctx width).canonicalFreshKey .bit
    (squareContext ctx width).canonicalFreshKey_fresh
  under6

/-- The actual widened original input cell in the final scratch context. -/
def wideCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord (width + width)) :=
  let head := CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh
  let under2 := head.underWorkspace (wideContext ctx width).canonicalFreshKey (.unsignedWord width)
    (wideContext ctx width).canonicalFreshKey_fresh
  let under3 := under2.underWorkspace
    (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
    (rootContext ctx width).canonicalFreshKey_fresh
  let under4 := under3.underWorkspace
    (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
    (halfContext ctx width).canonicalFreshKey_fresh
  let under5 := under4.underWorkspace
    (candidateContext ctx width).canonicalFreshKey (.unsignedWord (width + width))
    (candidateContext ctx width).canonicalFreshKey_fresh
  let under6 := under5.underWorkspace (squareContext ctx width).canonicalFreshKey .bit
    (squareContext ctx width).canonicalFreshKey_fresh
  under6

/-- The actual initial lower estimate cell in the final scratch context. -/
def rootCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord width) :=
  let head := CWriteRef.workspaceHead (wideContext ctx width)
    (wideContext ctx width).canonicalFreshKey (.unsignedWord width)
    (wideContext ctx width).canonicalFreshKey_fresh
  let under3 := head.underWorkspace (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
    (rootContext ctx width).canonicalFreshKey_fresh
  let under4 := under3.underWorkspace
    (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
    (halfContext ctx width).canonicalFreshKey_fresh
  let under5 := under4.underWorkspace
    (candidateContext ctx width).canonicalFreshKey (.unsignedWord (width + width))
    (candidateContext ctx width).canonicalFreshKey_fresh
  let under6 := under5.underWorkspace (squareContext ctx width).canonicalFreshKey .bit
    (squareContext ctx width).canonicalFreshKey_fresh
  under6

/-- The actual binary increment cell in the final scratch context. -/
def halfCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord width) :=
  let head := CWriteRef.workspaceHead (rootContext ctx width)
    (rootContext ctx width).canonicalFreshKey (.unsignedWord width)
    (rootContext ctx width).canonicalFreshKey_fresh
  let under4 := head.underWorkspace (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
    (halfContext ctx width).canonicalFreshKey_fresh
  let under5 := under4.underWorkspace
    (candidateContext ctx width).canonicalFreshKey (.unsignedWord (width + width))
    (candidateContext ctx width).canonicalFreshKey_fresh
  let under6 := under5.underWorkspace (squareContext ctx width).canonicalFreshKey .bit
    (squareContext ctx width).canonicalFreshKey_fresh
  under6

/-- The actual candidate midpoint cell in the final scratch context. -/
def candidateCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord width) :=
  let head := CWriteRef.workspaceHead (halfContext ctx width)
    (halfContext ctx width).canonicalFreshKey (.unsignedWord width)
    (halfContext ctx width).canonicalFreshKey_fresh
  let under5 := head.underWorkspace
    (candidateContext ctx width).canonicalFreshKey (.unsignedWord (width + width))
    (candidateContext ctx width).canonicalFreshKey_fresh
  let under6 := under5.underWorkspace (squareContext ctx width).canonicalFreshKey .bit
    (squareContext ctx width).canonicalFreshKey_fresh
  under6

/-- The actual full candidate square cell in the final scratch context. -/
def squareCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord (width + width)) :=
  let head := CWriteRef.workspaceHead (candidateContext ctx width)
    (candidateContext ctx width).canonicalFreshKey (.unsignedWord (width + width))
    (candidateContext ctx width).canonicalFreshKey_fresh
  let under6 := head.underWorkspace (squareContext ctx width).canonicalFreshKey .bit
    (squareContext ctx width).canonicalFreshKey_fresh
  under6

/-- The actual strict-comparison decision cell in the final scratch context. -/
def tooLargeCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) .bit :=
  let head := CWriteRef.workspaceHead (squareContext ctx width)
    (squareContext ctx width).canonicalFreshKey .bit
    (squareContext ctx width).canonicalFreshKey_fresh
  head

/-- Actual generated references consumed by each repeated refinement round. -/
def roundRefs (ctx : RuntimeCtx kind) (width : Nat) : RoundRefs (context ctx width) width where
  root := rootCell ctx width
  half := halfCell ctx width
  candidate := candidateCell ctx width
  square := squareCell ctx width
  tooLarge := tooLargeCell ctx width

/-- The scratch layout adds exactly its six real keys, preserving the original context tail. -/
theorem nativeSqrt_context_keys (ctx : RuntimeCtx kind) (width : Nat) :
    (context ctx width).keys =
      [(tooLargeCell ctx width).key, (squareCell ctx width).key, (candidateCell ctx width).key,
        (halfCell ctx width).key, (rootCell ctx width).key, (wideCell ctx width).key] ++ ctx.keys :=
  rfl

/-- The exact original quantum-wire list is unchanged by every real scratch allocation. -/
theorem nativeSqrt_context_quantumWires (ctx : RuntimeCtx kind) (width : Nat) :
    (context ctx width).quantumWires = ctx.quantumWires := rfl

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
