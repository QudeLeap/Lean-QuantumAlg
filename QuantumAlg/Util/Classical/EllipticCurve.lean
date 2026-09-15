/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.Classical.Modular.Additive
import all QuantumAlg.Util.Classical.EllipticCurve.Spec

/-!
# Fixed-width prime-field elliptic-curve semantics

This module is the quantum-free semantic boundary for fixed-width
short-Weierstrass elliptic curves.  A `CurveSpec` couples a fitted modulus to
the existing prime-field curve certificate and to Mathlib's affine
ellipticity witness.  Its point carrier is Mathlib's affine point type, so it
contains exactly one point at infinity and all finite points are already
nonsingular.

`Code` is intentionally a separate fixed-width representation.  Its infinity
representation is the single tagged word triple `(true, 0, 0)`; finite codes
are accepted only when both coordinates are canonical representatives and
satisfy the selected curve equation.  The operations below are semantic group
operations only.  They are deliberately not circuit constructions and this
module does not define scalar multiplication.
-/

section

namespace QuantumAlg
namespace ClassicalAlgorithms

namespace EllipticCurve

open Modular

noncomputable section

/-- The actual Mathlib affine point carrier for a fitted curve, including its
unique point at infinity. -/
abbrev Point {width : Nat} (spec : CurveSpec width) : Type :=
  spec.curve.MathlibPoint

namespace Point

/-- The carrier is already Mathlib's affine point type; this map makes the
agreement boundary explicit in public APIs. -/
def toMathlib {width : Nat} {spec : CurveSpec width} (point : Point spec) :
    spec.curve.MathlibPoint :=
  point

@[simp]
theorem toMathlib_apply {width : Nat} {spec : CurveSpec width}
    (point : Point spec) :
    point.toMathlib = point :=
  rfl

/-- The unique affine point at infinity. -/
def infinity {width : Nat} (spec : CurveSpec width) : Point spec :=
  0

theorem infinity_toMathlib {width : Nat} (spec : CurveSpec width) :
    (infinity spec).toMathlib = 0 :=
  rfl

/-- A point is at infinity exactly when it is Mathlib's additive identity. -/
def IsInfinity {width : Nat} {spec : CurveSpec width} (point : Point spec) : Prop :=
  point = 0

end Point

/-- A fixed-width external point representation.  `tag = true` denotes the
point-at-infinity form and `tag = false` denotes an affine coordinate pair. -/
structure Code (width : Nat) where
  /-- `true` denotes the unique infinity form; `false` denotes finite data. -/
  tag : Bool
  /-- Raw fixed-width affine `x` coordinate, validated separately. -/
  x : Word width
  /-- Raw fixed-width affine `y` coordinate, validated separately. -/
  y : Word width
deriving DecidableEq

namespace Code

/-- The only accepted code for the point at infinity. -/
def infinity (width : Nat) : Code width where
  tag := true
  x := wordOfNat width 0
  y := wordOfNat width 0

/-- The syntactic infinity form is accepted only with both coordinates zero. -/
def IsInfinity {width : Nat} (code : Code width) : Prop :=
  code.tag = true ∧ code.x.val = 0 ∧ code.y.val = 0

@[simp]
theorem infinity_isInfinity (width : Nat) :
    IsInfinity (infinity width) := by
  constructor
  · rfl
  · constructor <;> simp [infinity, wordOfNat]

/-- Interpret the stored `x` word as an element of the selected prime field.
The canonicality check remains separate in `IsFinite`. -/
def xField {width : Nat} (spec : CurveSpec width) (code : Code width) :
    ZMod spec.field.modulus :=
  code.x.val

/-- Interpret the stored `y` word as an element of the selected prime field.
The canonicality check remains separate in `IsFinite`. -/
def yField {width : Nat} (spec : CurveSpec width) (code : Code width) :
    ZMod spec.field.modulus :=
  code.y.val

/-- A finite code is untagged, has canonical coordinates, and lies on the
selected short-Weierstrass curve. -/
def IsFinite {width : Nat} (spec : CurveSpec width) (code : Code width) : Prop :=
  code.tag = false ∧
    code.x.val < spec.field.modulus ∧
    code.y.val < spec.field.modulus ∧
    spec.curve.AffineEquation (xField spec code) (yField spec code)

/-- The complete accepted language of fixed-width point codes. -/
def IsValid {width : Nat} (spec : CurveSpec width) (code : Code width) : Prop :=
  code.IsInfinity ∨ code.IsFinite spec

@[simp]
theorem infinity_isValid {width : Nat} (spec : CurveSpec width) :
    IsValid spec (infinity width) :=
  Or.inl (infinity_isInfinity width)

end Code

/-- Store a prime-field coordinate in the declared fixed-width word without
reduction.  The fitted-modulus proof supplies the required width bound. -/
def coordinateWord {width : Nat} (spec : CurveSpec width)
    (coordinate : ZMod spec.field.modulus) : Word width :=
  ⟨coordinate.val, (ZMod.val_lt coordinate).trans_le spec.field.le_capacity⟩

@[simp]
theorem coordinateWord_val {width : Nat} (spec : CurveSpec width)
    (coordinate : ZMod spec.field.modulus) :
    (coordinateWord spec coordinate).val = coordinate.val :=
  rfl

/-- Canonically encode a Mathlib affine point. -/
def encode {width : Nat} (spec : CurveSpec width) : Point spec → Code width
  | .zero => Code.infinity width
  | .some x y _ =>
      { tag := false
        x := coordinateWord spec x
        y := coordinateWord spec y }

/-- Decode exactly the accepted fixed-width codes into Mathlib affine points. -/
def decode {width : Nat} (spec : CurveSpec width) (code : Code width) :
    Option (Point spec) := by
  classical
  exact
    if hInfinity : code.IsInfinity then
      some 0
    else if hFinite : code.IsFinite spec then
      some (.some (Code.xField spec code) (Code.yField spec code)
        ((spec.affineEquation_iff_nonsingular (Code.xField spec code)
          (Code.yField spec code)).mp hFinite.2.2.2))
    else
      none

@[simp]
theorem encode_infinity {width : Nat} (spec : CurveSpec width) :
    encode spec (0 : Point spec) = Code.infinity width :=
  rfl

@[simp]
theorem decode_infinity {width : Nat} (spec : CurveSpec width) :
    decode spec (Code.infinity width) = some (0 : Point spec) := by
  simp [decode, Code.infinity_isInfinity]

/-- A finite Mathlib point encodes to an accepted finite code. -/
theorem encode_some_isFinite {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus)
    (h : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x y) :
    Code.IsFinite spec (encode spec (.some x y h : Point spec)) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact ZMod.val_lt x
  · exact ZMod.val_lt y
  · simpa [encode, Code.xField, Code.yField, coordinateWord,
      ZMod.natCast_zmod_val] using
      (spec.affineEquation_iff_nonsingular x y).mpr h

/-- Every encoded point is accepted by the external fixed-width code grammar. -/
theorem encode_isValid {width : Nat} (spec : CurveSpec width) (point : Point spec) :
    Code.IsValid spec (encode spec point) := by
  cases point with
  | zero =>
      exact Code.infinity_isValid spec
  | some x y h =>
      exact Or.inr (encode_some_isFinite spec x y h)

/-- Decoding a canonical encoding returns the original Mathlib point. -/
@[simp]
theorem decode_encode {width : Nat} (spec : CurveSpec width) (point : Point spec) :
    decode spec (encode spec point) = some point := by
  cases point with
  | zero =>
      exact decode_infinity spec
  | some x y h =>
      have hInfinity : ¬ Code.IsInfinity (encode spec (.some x y h : Point spec)) := by
        simp [encode, Code.IsInfinity]
      have hFinite : Code.IsFinite spec (encode spec (.some x y h : Point spec)) :=
        encode_some_isFinite spec x y h
      rw [decode, dif_neg hInfinity, dif_pos hFinite]
      simp only [encode, Code.xField, Code.yField, coordinateWord,
        ZMod.natCast_zmod_val]

/-- A successful decode certifies that the original external code was valid. -/
theorem decode_sound {width : Nat} (spec : CurveSpec width) (code : Code width)
    (point : Point spec) :
    decode spec code = some point → Code.IsValid spec code := by
  intro decoded
  by_cases hInfinity : code.IsInfinity
  · exact Or.inl hInfinity
  by_cases hFinite : code.IsFinite spec
  · exact Or.inr hFinite
  simp [decode, hInfinity, hFinite] at decoded

/-- Every valid external code decodes to a Mathlib affine point. -/
theorem decode_complete {width : Nat} (spec : CurveSpec width) (code : Code width)
    (valid : Code.IsValid spec code) :
    ∃ point : Point spec, decode spec code = some point := by
  rcases valid with hInfinity | hFinite
  · exact ⟨0, by simp [decode, hInfinity]⟩
  · have hNotInfinity : ¬ Code.IsInfinity code := by
      intro hInfinity
      simpa [hFinite.1] using hInfinity.1
    refine ⟨.some (Code.xField spec code) (Code.yField spec code)
      ((spec.affineEquation_iff_nonsingular (Code.xField spec code)
        (Code.yField spec code)).mp hFinite.2.2.2), ?_⟩
    simp [decode, hNotInfinity, hFinite]

/-- Invalid codes are rejected rather than being silently reduced modulo the
field modulus. -/
theorem decode_eq_none_of_not_isValid {width : Nat} (spec : CurveSpec width)
    (code : Code width) (invalid : ¬ Code.IsValid spec code) :
    decode spec code = none := by
  by_cases hInfinity : code.IsInfinity
  · exact (invalid (Or.inl hInfinity)).elim
  by_cases hFinite : code.IsFinite spec
  · exact (invalid (Or.inr hFinite)).elim
  simp [decode, hInfinity, hFinite]

/-- In particular, an untagged code with an out-of-range coordinate is
rejected; `decode` never treats a noncanonical word as its reduced residue. -/
theorem decode_rejects_noncanonical_finite {width : Nat} (spec : CurveSpec width)
    (code : Code width) (tag : code.tag = false)
    (outOfRange : ¬ code.x.val < spec.field.modulus ∨
      ¬ code.y.val < spec.field.modulus) :
    decode spec code = none := by
  apply decode_eq_none_of_not_isValid spec code
  intro valid
  rcases valid with hInfinity | hFinite
  · simpa [tag] using hInfinity.1
  · rcases outOfRange with xOutOfRange | yOutOfRange
    · exact xOutOfRange hFinite.2.1
    · exact yOutOfRange hFinite.2.2.1

/-- An untagged code outside the selected affine equation is rejected even
when its two words happen to be canonical field representatives. -/
theorem decode_rejects_offCurve {width : Nat} (spec : CurveSpec width)
    (code : Code width) (tag : code.tag = false)
    (offCurve : ¬ spec.curve.AffineEquation
      (Code.xField spec code) (Code.yField spec code)) :
    decode spec code = none := by
  apply decode_eq_none_of_not_isValid spec code
  intro valid
  rcases valid with hInfinity | hFinite
  · simpa [tag] using hInfinity.1
  · exact offCurve hFinite.2.2.2

/-- A tagged infinity code with a nonzero coordinate has no finite alias and
is rejected. -/
theorem decode_rejects_malformed_infinity {width : Nat} (spec : CurveSpec width)
    (code : Code width) (tag : code.tag = true)
    (malformed : code.x.val ≠ 0 ∨ code.y.val ≠ 0) :
    decode spec code = none := by
  apply decode_eq_none_of_not_isValid spec code
  intro valid
  rcases valid with hInfinity | hFinite
  · rcases malformed with xMalformed | yMalformed
    · exact xMalformed hInfinity.2.1
    · exact yMalformed hInfinity.2.2
  · simpa [tag] using hFinite.1

/-- The syntactic infinity form has no alternative code. -/
theorem code_eq_infinity_of_isInfinity {width : Nat} {code : Code width}
    (hInfinity : code.IsInfinity) :
    code = Code.infinity width := by
  cases code with
  | mk tag x y =>
      simp only [Code.IsInfinity] at hInfinity
      rcases hInfinity with ⟨rfl, xZero, yZero⟩
      simp only [Code.infinity, wordOfNat]
      congr
      · exact Fin.ext xZero
      · exact Fin.ext yZero

/-- No finite code can alias the unique point at infinity after decoding. -/
theorem decode_eq_some_infinity_iff {width : Nat} (spec : CurveSpec width)
    (code : Code width) :
    decode spec code = some (0 : Point spec) ↔ code = Code.infinity width := by
  constructor
  · intro decoded
    by_cases hInfinity : code.IsInfinity
    · exact code_eq_infinity_of_isInfinity hInfinity
    by_cases hFinite : code.IsFinite spec
    · simp [decode, hInfinity, hFinite] at decoded
    · simp [decode, hInfinity, hFinite] at decoded
  · intro codeInfinity
    subst code
    exact decode_infinity spec

/-- Every successful decode came from the unique canonical encoding of the
decoded point.  In particular, valid finite points have no noncanonical alias. -/
theorem encode_eq_of_decode_eq_some {width : Nat} (spec : CurveSpec width)
    (code : Code width) (point : Point spec)
    (decoded : decode spec code = some point) :
    encode spec point = code := by
  by_cases hInfinity : code.IsInfinity
  · have codeEq : code = Code.infinity width :=
      code_eq_infinity_of_isInfinity hInfinity
    subst code
    have pointEq : point = 0 := by
      simpa using decoded.symm
    subst point
    exact encode_infinity spec
  by_cases hFinite : code.IsFinite spec
  · rw [decode, dif_neg hInfinity, dif_pos hFinite] at decoded
    have pointEq :
        point = .some (Code.xField spec code) (Code.yField spec code)
          ((spec.affineEquation_iff_nonsingular (Code.xField spec code)
            (Code.yField spec code)).mp hFinite.2.2.2) := by
      exact Option.some.inj decoded.symm
    subst point
    cases code with
    | mk tag x y =>
        simp only [Code.IsFinite] at hFinite
        rcases hFinite with ⟨rfl, xRange, yRange, equation⟩
        simp only [encode, Code.xField, Code.yField, coordinateWord]
        congr
        · simp [Nat.mod_eq_of_lt xRange]
        · simp [Nat.mod_eq_of_lt yRange]
  · simp [decode, hInfinity, hFinite] at decoded

/-- Encoding is injective because `decode` is its left inverse. -/
theorem encode_injective {width : Nat} (spec : CurveSpec width) :
    Function.Injective (encode spec) := by
  intro left right encoded
  have decoded := congrArg (decode spec) encoded
  simpa using decoded

/-- The code emitted for infinity is unique among all point encodings. -/
theorem encode_eq_infinity_iff {width : Nat} (spec : CurveSpec width)
    (point : Point spec) :
    encode spec point = Code.infinity width ↔ point = 0 := by
  constructor
  · intro encoded
    have decoded := congrArg (decode spec) encoded
    simpa using decoded
  · intro pointZero
    subst point
    exact encode_infinity spec

namespace Point

/-- A Mathlib point is valid for this external representation when some
accepted fixed-width code decodes to it. -/
def IsValid {width : Nat} (spec : CurveSpec width) (point : Point spec) : Prop :=
  ∃ code : Code width, decode spec code = some point

/-- Every point in the intrinsic Mathlib carrier has a canonical fixed-width
encoding. -/
theorem isValid {width : Nat} (spec : CurveSpec width) (point : Point spec) :
    Point.IsValid spec point :=
  ⟨encode spec point, decode_encode spec point⟩

end Point

namespace Neg

/-- Complete semantic negation, delegated to Mathlib's affine group law. -/
def eval {width : Nat} (spec : CurveSpec width) (point : Point spec) : Point spec :=
  -point

/-- `Neg.eval` is definitionally the Mathlib affine-point negation. -/
theorem eval_toMathlib {width : Nat} (spec : CurveSpec width) (point : Point spec) :
    (eval spec point).toMathlib = -point.toMathlib :=
  rfl

@[simp]
theorem eval_infinity {width : Nat} (spec : CurveSpec width) :
    eval spec 0 = 0 :=
  neg_zero

@[simp]
theorem eval_involutive {width : Nat} (spec : CurveSpec width)
    (point : Point spec) :
    eval spec (eval spec point) = point :=
  neg_neg point

/-- Negation returns a point with a canonical fixed-width encoding. -/
theorem eval_isValid {width : Nat} (spec : CurveSpec width) (point : Point spec) :
    Point.IsValid spec (eval spec point) :=
  Point.isValid spec _

end Neg

namespace Add

/-- The semantic branch selected by affine addition.  The inverse branch also
covers the vertical-line case, including finite points whose sum is infinity. -/
inductive Branch where
  | leftInfinity
  | rightInfinity
  | inverseOrVertical
  | doubling
  | generic
deriving DecidableEq, Repr

/-- Classify the total affine addition case before applying the group law.
The order makes the two infinity cases explicit and gives inverse/vertical
precedence over doubling for order-two points. -/
def branch {width : Nat} (spec : CurveSpec width)
    (left right : Point spec) : Branch :=
  if left = 0 then .leftInfinity
  else if right = 0 then .rightInfinity
  else if left = -right then .inverseOrVertical
  else if left = right then .doubling
  else .generic

/-- Complete semantic affine addition, including infinity and vertical cases. -/
def eval {width : Nat} (spec : CurveSpec width)
    (left right : Point spec) : Point spec :=
  left + right

/-- `Add.eval` agrees definitionally with Mathlib's affine-point group law. -/
theorem eval_toMathlib {width : Nat} (spec : CurveSpec width)
    (left right : Point spec) :
    (eval spec left right).toMathlib = left.toMathlib + right.toMathlib :=
  rfl

@[simp]
theorem branch_leftInfinity {width : Nat} (spec : CurveSpec width)
    (right : Point spec) :
    branch spec 0 right = .leftInfinity := by
  simp [branch]

theorem branch_rightInfinity {width : Nat} (spec : CurveSpec width)
    (left right : Point spec) (leftNonzero : left ≠ 0) (rightZero : right = 0) :
    branch spec left right = .rightInfinity := by
  simp [branch, leftNonzero, rightZero]

theorem branch_inverseOrVertical {width : Nat} (spec : CurveSpec width)
    (left right : Point spec) (_leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0)
    (inverse : left = -right) :
    branch spec left right = .inverseOrVertical := by
  simp [branch, rightNonzero, inverse]

theorem branch_doubling {width : Nat} (spec : CurveSpec width)
    (point : Point spec) (nonzero : point ≠ 0) (notInverse : point ≠ -point) :
    branch spec point point = .doubling := by
  simp [branch, nonzero, notInverse]

theorem branch_generic {width : Nat} (spec : CurveSpec width)
    (left right : Point spec) (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0)
    (notInverse : left ≠ -right) (distinct : left ≠ right) :
    branch spec left right = .generic := by
  simp [branch, leftNonzero, rightNonzero, notInverse, distinct]

@[simp]
theorem eval_left_infinity {width : Nat} (spec : CurveSpec width)
    (point : Point spec) :
    eval spec 0 point = point :=
  zero_add point

@[simp]
theorem eval_right_infinity {width : Nat} (spec : CurveSpec width)
    (point : Point spec) :
    eval spec point 0 = point :=
  add_zero point

@[simp]
theorem eval_inverse {width : Nat} (spec : CurveSpec width)
    (point : Point spec) :
    eval spec point (-point) = 0 :=
  add_neg_cancel point

/-- Addition always returns an intrinsically valid Mathlib point, hence a
point with a canonical fixed-width encoding. -/
theorem eval_isValid {width : Nat} (spec : CurveSpec width)
    (left right : Point spec) :
    Point.IsValid spec (eval spec left right) :=
  Point.isValid spec _

end Add

namespace Double

/-- Complete semantic point doubling. -/
def eval {width : Nat} (spec : CurveSpec width) (point : Point spec) : Point spec :=
  Add.eval spec point point

/-- Doubling agrees definitionally with adding the Mathlib point to itself. -/
theorem eval_toMathlib {width : Nat} (spec : CurveSpec width) (point : Point spec) :
    (eval spec point).toMathlib = point.toMathlib + point.toMathlib :=
  rfl

theorem eval_infinity {width : Nat} (spec : CurveSpec width) :
    eval spec 0 = 0 :=
  Add.eval_left_infinity spec 0

@[simp]
theorem eval_eq_add_self {width : Nat} (spec : CurveSpec width)
    (point : Point spec) :
    eval spec point = Add.eval spec point point :=
  rfl

theorem eval_isValid {width : Nat} (spec : CurveSpec width) (point : Point spec) :
    Point.IsValid spec (eval spec point) :=
  Point.isValid spec _

end Double

namespace Sub

/-- Complete semantic point subtraction. -/
def eval {width : Nat} (spec : CurveSpec width)
    (left right : Point spec) : Point spec :=
  left - right

/-- `Sub.eval` agrees definitionally with Mathlib's affine-point subtraction. -/
theorem eval_toMathlib {width : Nat} (spec : CurveSpec width)
    (left right : Point spec) :
    (eval spec left right).toMathlib = left.toMathlib - right.toMathlib :=
  rfl

@[simp]
theorem eval_right_infinity {width : Nat} (spec : CurveSpec width)
    (point : Point spec) :
    eval spec point 0 = point :=
  sub_zero point

@[simp]
theorem eval_self {width : Nat} (spec : CurveSpec width)
    (point : Point spec) :
    eval spec point point = 0 :=
  sub_self point

theorem eval_isValid {width : Nat} (spec : CurveSpec width)
    (left right : Point spec) :
    Point.IsValid spec (eval spec left right) :=
  Point.isValid spec _

end Sub

end

end EllipticCurve

end ClassicalAlgorithms
end QuantumAlg

end
