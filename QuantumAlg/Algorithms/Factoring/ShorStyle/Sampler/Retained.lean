/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program

/-!
# Actual retained sample and complete RSA parameter

Two real retention instructions allocate the packed random sample and the
full unit/factor parameter. One native uniform random instruction fills the
sample. The actual scoped preparation then computes the parameter. Both
retained values and every original caller system remain live in the result.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained

open Execution
open ClassicalRoutines

variable {kind : ProblemKind}

/-- Actual retained source bits, before allocating the separate complete parameter. -/
def sampleContext (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  ctx.addRetained ctx.canonicalFreshKey (.bits (residueSamplingBits N))
    ctx.canonicalFreshKey_fresh

/-- The complete caller context with its two real retained results. -/
public def context (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (sampleContext ctx N).addRetained (sampleContext ctx N).canonicalFreshKey
    (ParameterShape (modulusBits N)) (sampleContext ctx N).canonicalFreshKey_fresh

/-- The actual retained sample cell, lifted past the subsequent parameter allocation. -/
def sampleRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) (.bits (residueSamplingBits N)) :=
  (CWriteRef.retainedHead ctx ctx.canonicalFreshKey (.bits (residueSamplingBits N))
    ctx.canonicalFreshKey_fresh).underRetained (sampleContext ctx N).canonicalFreshKey
      (ParameterShape (modulusBits N)) (sampleContext ctx N).canonicalFreshKey_fresh

/-- The parameter contains the unit and every early-factor tag and payload bit. -/
def parameterRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) (ParameterShape (modulusBits N)) :=
  CWriteRef.retainedHead (sampleContext ctx N) (sampleContext ctx N).canonicalFreshKey
    (ParameterShape (modulusBits N)) (sampleContext ctx N).canonicalFreshKey_fresh

/-- Two genuine retention instructions allocate precisely those two result cells. -/
def allocation (ctx : RuntimeCtx kind) (N : Nat) : Circuit ctx (context ctx N) :=
  .seq (.retain ctx ctx.canonicalFreshKey (.bits (residueSamplingBits N))
    ctx.canonicalFreshKey_fresh)
    (.retain (sampleContext ctx N) (sampleContext ctx N).canonicalFreshKey
      (ParameterShape (modulusBits N)) (sampleContext ctx N).canonicalFreshKey_fresh)

/-- Draw the actual source sample and execute the expanded native parameter preparation. -/
def body (ctx : RuntimeCtx kind) (N : Nat) : Circuit (context ctx N) (context ctx N) :=
  .seq (PackedSample.draw N (sampleRef ctx N))
    (Program.circuit N (FirstAccepted.cellRead (sampleRef ctx N)) (parameterRef ctx N))

/-- The complete native residue sampler retains its source sample and full computed parameter. -/
def circuit (ctx : RuntimeCtx kind) (N : Nat) : Circuit ctx (context ctx N) :=
  .seq (allocation ctx N) (body ctx N)

/-- The exact store extension produced by the two real retention instructions. -/
def pushStore {ctx : RuntimeCtx kind} (N : Nat) (store : Store ctx) : Store (context ctx N) :=
  (store.pushRetained ctx.canonicalFreshKey (.bits (residueSamplingBits N))
    ctx.canonicalFreshKey_fresh).pushRetained (sampleContext ctx N).canonicalFreshKey
      (ParameterShape (modulusBits N)) (sampleContext ctx N).canonicalFreshKey_fresh

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
