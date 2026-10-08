/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Repack
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Coefficient
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Mul
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub

/-!
# Actual common affine addition tail

The original total coefficient producer precedes three modular products,
four original modular subtractions and the final nominal point adapter.
Eight actual word cells and the original false tag are allocated internally,
in their original order. Both finite addition branches use this same tail.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Deepest-first shapes preserve coefficient through Y-output allocation, then the false tag. -/
def affineShapes (width : Nat) : List CShape :=
  [.bit, .unsignedWord width, .unsignedWord width, .unsignedWord width,
    .unsignedWord width, .unsignedWord width, .unsignedWord width,
    .unsignedWord width, .unsignedWord width]

/-- Original eight arithmetic cells and the actual internally initialized nominal tag. -/
structure AffineScratch (ctx : RuntimeCtx kind) (width : Nat) where
  coefficient : CWriteRef ctx (.unsignedWord width)
  slope : CWriteRef ctx (.unsignedWord width)
  slopeSquared : CWriteRef ctx (.unsignedWord width)
  xPartial : CWriteRef ctx (.unsignedWord width)
  xOutput : CWriteRef ctx (.unsignedWord width)
  xDifference : CWriteRef ctx (.unsignedWord width)
  yProduct : CWriteRef ctx (.unsignedWord width)
  yOutput : CWriteRef ctx (.unsignedWord width)
  tag : CWriteRef ctx .bit

/-- Structural references to all original roles in the actual allocated cells. -/
def affineScratch (cells : Cells ctx (affineShapes width)) : AffineScratch ctx width where
  coefficient := (cellAt cells ⟨8, by change 8 < 9; decide⟩).ref
  slope := (cellAt cells ⟨7, by change 7 < 9; decide⟩).ref
  slopeSquared := (cellAt cells ⟨6, by change 6 < 9; decide⟩).ref
  xPartial := (cellAt cells ⟨5, by change 5 < 9; decide⟩).ref
  xOutput := (cellAt cells ⟨4, by change 4 < 9; decide⟩).ref
  xDifference := (cellAt cells ⟨3, by change 3 < 9; decide⟩).ref
  yProduct := (cellAt cells ⟨2, by change 2 < 9; decide⟩).ref
  yOutput := (cellAt cells ⟨1, by change 1 < 9; decide⟩).ref
  tag := (cellAt cells ⟨0, by change 0 < 9; decide⟩).ref

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Every original total arithmetic call occurs in its original chronological position. -/
def affineStage (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width)) :
    Fin 9 → Circuit model ctx ctx :=
  ![Field.Native.coefficientIntoWord spec denominator scratch.coefficient,
    Field.Native.mulIntoWord spec numerator (classifierRead scratch.coefficient) scratch.slope,
    Field.Native.mulIntoWord spec (classifierRead scratch.slope) (classifierRead scratch.slope)
      scratch.slopeSquared,
    Field.Native.subIntoWord spec (classifierRead scratch.slopeSquared) leftX scratch.xPartial,
    Field.Native.subIntoWord spec (classifierRead scratch.xPartial) rightX scratch.xOutput,
    Field.Native.subIntoWord spec leftX (classifierRead scratch.xOutput) scratch.xDifference,
    Field.Native.mulIntoWord spec (classifierRead scratch.slope)
      (classifierRead scratch.xDifference)
      scratch.yProduct,
    Field.Native.subIntoWord spec (classifierRead scratch.yProduct) leftY scratch.yOutput,
    repackRawInto (.product (classifierRead scratch.tag)
      (.product (classifierRead scratch.xOutput) (classifierRead scratch.yOutput))) output]

/-- The same actual right-associated nine-call tail is shared by both finite branches. -/
def affineBody (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width)) :
    Circuit model ctx ctx :=
  Circuit.forRange 9 (affineStage spec leftX rightX leftY numerator denominator scratch output)

/-- All original tail scratch is actually allocated and released; no caller tag is required. -/
def affineInto (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width)) : Circuit model ctx ctx :=
  withCells ctx (affineShapes width) fun cells _ transport _ =>
    affineBody spec (transport.liftInput leftX) (transport.liftInput rightX)
      (transport.liftInput leftY) (transport.liftInput numerator) (transport.liftInput denominator)
      (affineScratch cells) (transport.liftWrite output)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
