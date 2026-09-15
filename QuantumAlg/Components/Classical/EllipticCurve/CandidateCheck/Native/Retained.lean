/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native

/-!
# Original retained candidate-verification outputs

The actual acceptance bit is retained first, then the scalar point. Both
remain live after the original four verification stages. All operands are
structural lifts of the original caller inputs under these two fresh cells.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

/-- The original acceptance result is the first actual retained allocation. -/
def acceptedCtx (ctx : RuntimeCtx kind) : RuntimeCtx kind :=
  ctx.addRetained ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh

/-- The scalar result is retained after the original acceptance bit. -/
def retainedCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (acceptedCtx ctx).addRetained (acceptedCtx ctx).canonicalFreshKey (PointShape width)
    (acceptedCtx ctx).canonicalFreshKey_fresh

/-- The original acceptance destination stays live under the subsequent scalar result. -/
def retainedAccepted (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (retainedCtx ctx width) .bit :=
  (CWriteRef.retainedHead ctx ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh).underRetained
    (acceptedCtx ctx).canonicalFreshKey (PointShape width)
    (acceptedCtx ctx).canonicalFreshKey_fresh

/-- The original scalar multiplication writes the second actual retained cell. -/
def retainedScalar (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (retainedCtx ctx width) (PointShape width) :=
  CWriteRef.retainedHead (acceptedCtx ctx) (acceptedCtx ctx).canonicalFreshKey
    (PointShape width) (acceptedCtx ctx).canonicalFreshKey_fresh

/-- Original structural inputs are transported through both actual retained allocations. -/
def retainedInput (width : Nat) {shape : CShape} (input : CInputRef ctx shape) :
    CInputRef (retainedCtx ctx width) shape :=
  (input.underRetained ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh).underRetained
    (acceptedCtx ctx).canonicalFreshKey (PointShape width)
    (acceptedCtx ctx).canonicalFreshKey_fresh

/-- Both original retained outputs are allocated in their original chronological order. -/
def retainOutputs (ctx : RuntimeCtx kind) (width : Nat) :
    Circuit ctx (retainedCtx ctx width) :=
  .seq (.retain ctx ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh)
    (.retain (acceptedCtx ctx) (acceptedCtx ctx).canonicalFreshKey (PointShape width)
      (acceptedCtx ctx).canonicalFreshKey_fresh)

/-- Retain both original outputs, then execute all four original actual verification stages. -/
def retainedCircuit (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit) :
    Circuit ctx (retainedCtx ctx width) :=
  .seq (retainOutputs ctx width)
    (verifyInto spec (retainedInput width candidate) (retainedInput width base)
      (retainedInput width target) (retainedInput width inverseSuccess)
      (retainedInput width reconstruction) (retainedScalar ctx width) (retainedAccepted ctx width))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
