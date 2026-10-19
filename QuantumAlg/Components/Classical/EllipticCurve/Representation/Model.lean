/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Util.Classical.EllipticCurve

/-!
# Pure canonical fixed-width point representations

The original nominal shape, raw code adapters and mathematical representation
predicates retain their full names and bodies independently of machine storage.
Infinity has its original unique tagged zero-coordinate code; affine coordinates
remain canonical field representatives validated by the original decoder.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve

open ClassicalAlgorithms ClassicalAlgorithms.EllipticCurve

noncomputable section

namespace Pure

/-- An intrinsically valid pure point on the supplied curve. -/
abbrev Point {width : Nat}
    (spec : CurveSpec width) :=
  ClassicalAlgorithms.EllipticCurve.Point spec
/-- A raw fixed-width code consumed by point decoding. -/
abbrev Code (width : Nat) :=
  ClassicalAlgorithms.EllipticCurve.Code width

end Pure

/-- The nominal Core storage shape for one raw elliptic-curve code. -/
abbrev PointShape (width : Nat) : CShape :=
  .ellipticCurvePoint width

/-- Two point encodings kept structurally separate for binary operations. -/
abbrev PointPairShape (width : Nat) : CShape :=
  .product (PointShape width) (PointShape width)

/-- Failure or one canonical point encoding. -/
abbrev PointOptionShape (width : Nat) : CShape :=
  .option (PointShape width)

/-- Store a pure raw code in Core's nominal point carrier. -/
def encodeCode {width : Nat} (code : Pure.Code width) :
    CShape.Value (PointShape width) :=
  .ellipticCurvePoint code.tag code.x code.y

/-- Recover a pure raw code without assigning curve validity. -/
def decodeCode {width : Nat} : CShape.Value (PointShape width) → Pure.Code width
  | .ellipticCurvePoint tag x y => ⟨tag, x, y⟩

@[simp]
lemma decodeCode_encodeCode {width : Nat} (code : Pure.Code width) :
    decodeCode (encodeCode code) = code := by
  cases code
  rfl

@[simp]
lemma encodeCode_decodeCode {width : Nat}
    (encoded : CShape.Value (PointShape width)) :
    encodeCode (decodeCode encoded) = encoded := by
  cases encoded
  rfl

/-- Exact structural representation of one raw external code. -/
def CodeRepresents {width : Nat} (encoded : CShape.Value (PointShape width))
    (code : Pure.Code width) : Prop :=
  decodeCode encoded = code

/-- A nominal point represents a semantic point exactly when pure decoding
accepts its raw code as that point. -/
def PointRepresents {width : Nat} (spec : CurveSpec width)
    (encoded : CShape.Value (PointShape width)) (point : Pure.Point spec) : Prop :=
  ClassicalAlgorithms.EllipticCurve.decode spec
      (decodeCode encoded) = some point

/-- Public point validity retains a semantic point witness. -/
def PointValid {width : Nat} (spec : CurveSpec width)
    (encoded : CShape.Value (PointShape width)) : Prop :=
  ∃ point : Pure.Point spec, PointRepresents spec encoded point

/-- Canonically encode one intrinsically valid semantic point. -/
def encodePoint {width : Nat} (spec : CurveSpec width)
    (point : Pure.Point spec) : CShape.Value (PointShape width) :=
  encodeCode (ClassicalAlgorithms.EllipticCurve.encode spec point)

@[simp]
lemma decodeCode_encodePoint {width : Nat} (spec : CurveSpec width)
    (point : Pure.Point spec) :
    decodeCode (encodePoint spec point) =
      ClassicalAlgorithms.EllipticCurve.encode spec point := by
  simp [encodePoint]

lemma encodePoint_represents {width : Nat} (spec : CurveSpec width)
    (point : Pure.Point spec) :
    PointRepresents spec (encodePoint spec point) point := by
  simp [PointRepresents, encodePoint]

lemma encodePoint_valid {width : Nat} (spec : CurveSpec width)
    (point : Pure.Point spec) : PointValid spec (encodePoint spec point) :=
  ⟨point, encodePoint_represents spec point⟩

end

end QuantumAlg.ClassicalRoutines.EllipticCurve
