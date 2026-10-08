/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Representation.Model
import all QuantumAlg.Components.Classical.Model.BitWord.Selection
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Original complete nominal point equality

This pure comparison includes the infinity tag and both raw coordinate words.
Its declarations retain their original full names and proof bodies.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.PointEquality

open ClassicalAlgorithms ClassicalAlgorithms.Modular

noncomputable section

/-- The raw tag-and-coordinate product exposed by the nominal point adapter. -/
abbrev RawPointShape (width : Nat) : CShape :=
  .product .bit (.product (.unsignedWord width) (.unsignedWord width))

/-- The pure Boolean tested by a complete nominal point comparison. -/
def pointEqual {width : Nat} (left right : CShape.Value (PointShape width)) : Bool :=
  decide (decodeCode left = decodeCode right)

/-- The pure comparison accepts exactly structurally equal nominal points. -/
theorem pointEqual_eq_true_iff {width : Nat}
    (left right : CShape.Value (PointShape width)) :
    pointEqual left right = true ↔ left = right := by
  cases left
  cases right
  simp [pointEqual, decodeCode]

/-- Structural equality is exactly tag equality conjoined with both coordinate
equalities. -/
theorem pointEqual_eq_components {width : Nat}
    (left right : CShape.Value (PointShape width)) :
    pointEqual left right =
      (!(Bool.xor left.ellipticCurvePointInfinityTag
          right.ellipticCurvePointInfinityTag) &&
        (decide (left.ellipticCurvePointX = right.ellipticCurvePointX) &&
          decide (left.ellipticCurvePointY = right.ellipticCurvePointY))) := by
  cases left with
  | ellipticCurvePoint leftTag leftX leftY =>
      cases right with
      | ellipticCurvePoint rightTag rightX rightY =>
          cases leftTag <;> cases rightTag <;>
            simp [pointEqual, decodeCode,
              CShape.Value.ellipticCurvePointInfinityTag,
              CShape.Value.ellipticCurvePointX,
              CShape.Value.ellipticCurvePointY]

/-- Exact sequence of classical events emitted by the structural core. -/
def coreTrace (model : ExecutionModel) [BitWord.Selected model]
    (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.nominalEncoding (.unpackEllipticCurvePoint width))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.nominalEncoding (.unpackEllipticCurvePoint width))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .xor)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .equal width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .equal width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .and)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .and))]

/-- Exact syntax-derived resource envelope of one structural comparison. -/
def coreEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (width : Nat) : ResourcePool model :=
  ResourcePool.ofList (coreTrace model width)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.PointEquality
