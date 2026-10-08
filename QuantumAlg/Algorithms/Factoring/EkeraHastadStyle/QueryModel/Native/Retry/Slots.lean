/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional

/-!
# Actual selector cells before the original-width oracle bank

The accepted flag, selected word and optional-unpack product are retained
once, before source sampling and quantum preparation. The same three cells
serve every batch. Their real default values provide the initially empty
selection; no caller-supplied initial flag is part of the constructor.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry.Slots

open Execution

variable {kind : ProblemKind}

/-- The first retained selector cell is its accepted flag. -/
def acceptedContext (ctx : RuntimeCtx kind) : RuntimeCtx kind :=
  ctx.addRetained ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh

/-- The next actual cell stores the first accepted word. -/
def selectedContext (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (acceptedContext ctx).addRetained (acceptedContext ctx).canonicalFreshKey
    (.unsignedWord width) (acceptedContext ctx).canonicalFreshKey_fresh

/-- One further product cell receives each real optional unpack instruction. -/
def context (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (selectedContext ctx width).addRetained (selectedContext ctx width).canonicalFreshKey
    (.product .bit (.unsignedWord width)) (selectedContext ctx width).canonicalFreshKey_fresh

/-- The accepted flag keeps its identity beneath both later selector allocations. -/
def acceptedRef (ctx : RuntimeCtx kind) (width : Nat) : CWriteRef (context ctx width) .bit :=
  ((CWriteRef.retainedHead ctx ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh).underRetained
    (acceptedContext ctx).canonicalFreshKey (.unsignedWord width)
    (acceptedContext ctx).canonicalFreshKey_fresh).underRetained
      (selectedContext ctx width).canonicalFreshKey (.product .bit (.unsignedWord width))
      (selectedContext ctx width).canonicalFreshKey_fresh

/-- The selected word is the actual second retained cell. -/
def selectedRef (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord width) :=
  (CWriteRef.retainedHead (acceptedContext ctx) (acceptedContext ctx).canonicalFreshKey
    (.unsignedWord width) (acceptedContext ctx).canonicalFreshKey_fresh).underRetained
      (selectedContext ctx width).canonicalFreshKey (.product .bit (.unsignedWord width))
      (selectedContext ctx width).canonicalFreshKey_fresh

/-- Every batch overwrites this same real decoded-candidate product cell. -/
def unpackedRef (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.product .bit (.unsignedWord width)) :=
  CWriteRef.retainedHead (selectedContext ctx width) (selectedContext ctx width).canonicalFreshKey
    (.product .bit (.unsignedWord width)) (selectedContext ctx width).canonicalFreshKey_fresh

/-- Three actual retention instructions initialize the persistent selection cells. -/
def allocate {model : ExecutionModel} (ctx : RuntimeCtx model.kind) (width : Nat) :
    Circuit model ctx (context ctx width) :=
  .seq (.retain ctx ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh)
    (.seq (.retain (acceptedContext ctx) (acceptedContext ctx).canonicalFreshKey
      (.unsignedWord width) (acceptedContext ctx).canonicalFreshKey_fresh)
      (.retain (selectedContext ctx width) (selectedContext ctx width).canonicalFreshKey
        (.product .bit (.unsignedWord width)) (selectedContext ctx width).canonicalFreshKey_fresh))

/-- The real selector allocation contributes no quantum wire. -/
theorem nativeOracle_retrySlots_wires (ctx : RuntimeCtx kind) (width : Nat) :
    (context ctx width).quantumWires = ctx.quantumWires := by
  simp only [context, selectedContext, acceptedContext, RuntimeCtx.quantumWires_addRetained]

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry.Slots
