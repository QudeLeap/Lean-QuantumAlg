/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Affine
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Add

/-!
# Actual original finite doubling arm

The original product, two additions, public curve-coefficient loader and two
further additions prepare the original numerator and denominator. Six real
lexical words precede the unchanged total affine tail, in the original order.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original canonical raw word for the public short-Weierstrass coefficient. -/
def doublingCurveAWord (spec : CurveSpec width) : CShape.Word width :=
  .unsignedWord (coordinateWord spec spec.curve.a)

/-- The six actual prefix cells, listed deepest first in their original allocation order. -/
def doublingShapes (width : Nat) : List CShape :=
  [.unsignedWord width, .unsignedWord width, .unsignedWord width,
    .unsignedWord width, .unsignedWord width, .unsignedWord width]

/-- The original materialized square, doubled/tripled square, coefficient and slope operands. -/
structure DoublingScratch (ctx : RuntimeCtx kind) (width : Nat) where
  xSquared : CWriteRef ctx (.unsignedWord width)
  doubledXSquared : CWriteRef ctx (.unsignedWord width)
  tripledXSquared : CWriteRef ctx (.unsignedWord width)
  a : CWriteRef ctx (.unsignedWord width)
  numerator : CWriteRef ctx (.unsignedWord width)
  denominator : CWriteRef ctx (.unsignedWord width)

/-- Typed references preserve the exact six original chronological roles. -/
def doublingScratch (cells : Cells ctx (doublingShapes width)) : DoublingScratch ctx width where
  xSquared := (cellAt cells ⟨5, by change 5 < 6; decide⟩).ref
  doubledXSquared := (cellAt cells ⟨4, by change 4 < 6; decide⟩).ref
  tripledXSquared := (cellAt cells ⟨3, by change 3 < 6; decide⟩).ref
  a := (cellAt cells ⟨2, by change 2 < 6; decide⟩).ref
  numerator := (cellAt cells ⟨1, by change 1 < 6; decide⟩).ref
  denominator := (cellAt cells ⟨0, by change 0 < 6; decide⟩).ref

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Every arithmetic and constant-loading call precedes the original tail in its original slot. -/
def doublingStage (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width)) :
    Fin 7 → Circuit model ctx ctx :=
  ![Field.Native.mulIntoWord spec.field pointX pointX scratch.xSquared,
    Field.Native.addIntoWord spec.field (classifierRead scratch.xSquared)
      (classifierRead scratch.xSquared) scratch.doubledXSquared,
    Field.Native.addIntoWord spec.field (classifierRead scratch.doubledXSquared)
      (classifierRead scratch.xSquared) scratch.tripledXSquared,
    ConstantWord.circuit scratch.a (doublingCurveAWord spec).toNat,
    Field.Native.addIntoWord spec.field (classifierRead scratch.tripledXSquared)
      (classifierRead scratch.a) scratch.numerator,
    Field.Native.addIntoWord spec.field pointY pointY scratch.denominator,
    affineInto spec.field pointX pointX pointY (classifierRead scratch.numerator)
      (classifierRead scratch.denominator) output]

/-- The original seven chronological calls, each retaining its actual internal work scopes. -/
def doublingBody (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width)) :
    Circuit model ctx ctx :=
  Circuit.forRange 7 (doublingStage spec pointX pointY scratch output)

/-- Allocate all original doubling-prefix cells and retain the complete actual point snapshot. -/
def doublingInto (spec : CurveSpec width)
    (point : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) : Circuit model ctx ctx :=
  withCells ctx (doublingShapes width) fun cells _ transport _ =>
    let pointAt := transport.liftInput point
    doublingBody spec (.first (.second pointAt)) (.second (.second pointAt))
      (doublingScratch cells) (transport.liftWrite output)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
