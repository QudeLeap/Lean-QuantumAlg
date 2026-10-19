/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.Classical.EllipticCurve

/-!
# Short-Weierstrass coordinate formulae for fixed-width curves

This module gives reusable pure coordinate formulae for the finite branches of
the complete point operations in `FixedWidth.EllipticCurve`.  It does not
choose a circuit implementation or a division routine: all denominators are
proved nonzero and are exposed as units over the prime field.  The resulting
points are proved equal to Mathlib's affine group operation.
-/

section

namespace QuantumAlg
namespace ClassicalAlgorithms

namespace EllipticCurve
namespace ShortWeierstrass

noncomputable section

/-- The finite `y` coordinate of a negated short-Weierstrass point. -/
def negY {width : Nat} (spec : CurveSpec width)
    (y : ZMod spec.field.modulus) : ZMod spec.field.modulus :=
  -y

/-- Mathlib's affine negation coordinate specializes to `-y` on the stored
short-Weierstrass curve. -/
lemma mathlib_negY_eq_negY {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus) :
    spec.curve.toWeierstrassCurve.toAffine.negY x y = negY spec y := by
  simp [negY,
    QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.toWeierstrassCurve,
    WeierstrassCurve.Affine.negY]

/-- Nonsingularity of a finite point is preserved by the short-form coordinate
negation. -/
lemma neg_nonsingular {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus)
    (h : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x y) :
    spec.curve.toWeierstrassCurve.toAffine.Nonsingular x (negY spec y) := by
  rw [← mathlib_negY_eq_negY]
  exact (WeierstrassCurve.Affine.nonsingular_neg
    (W' := spec.curve.toWeierstrassCurve.toAffine) x y).mpr h

/-- Finite negation has unchanged `x` coordinate and `-y` as its `y`
coordinate. -/
lemma neg_eval_some {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus)
    (h : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x y) :
    Neg.eval spec (.some x y h : Point spec) =
      (.some x (negY spec y) (neg_nonsingular spec x y h) : Point spec) := by
  change -(.some x y h : Point spec) = _
  rw [WeierstrassCurve.Affine.Point.neg_some]
  simp only [mathlib_negY_eq_negY]

/-- The conventional secant numerator `y₂ - y₁`. -/
def genericAddNumerator {width : Nat} (spec : CurveSpec width)
    (y₁ y₂ : ZMod spec.field.modulus) : ZMod spec.field.modulus :=
  y₂ - y₁

/-- The conventional secant denominator `x₂ - x₁`. -/
def genericAddDenominator {width : Nat} (spec : CurveSpec width)
    (x₁ x₂ : ZMod spec.field.modulus) : ZMod spec.field.modulus :=
  x₂ - x₁

/-- Distinct `x` coordinates make the conventional secant denominator
nonzero. -/
lemma genericAddDenominator_ne_zero {width : Nat} (spec : CurveSpec width)
    {x₁ x₂ : ZMod spec.field.modulus} (distinct : x₁ ≠ x₂) :
    genericAddDenominator spec x₁ x₂ ≠ 0 := by
  simpa [genericAddDenominator] using sub_ne_zero.mpr distinct.symm

/-- In the prime field, the generic-addition denominator is a unit. -/
lemma genericAddDenominator_isUnit {width : Nat} (spec : CurveSpec width)
    {x₁ x₂ : ZMod spec.field.modulus} (distinct : x₁ ≠ x₂) :
    IsUnit (genericAddDenominator spec x₁ x₂) :=
  isUnit_iff_ne_zero.mpr (genericAddDenominator_ne_zero spec distinct)

/-- Two finite points selected by the generic branch have distinct affine
`x` coordinates.  Equality of the coordinates would make the points equal or
negatives of one another, exactly the two branches already excluded. -/
lemma genericFinite_x_ne {width : Nat} (spec : CurveSpec width)
    (x₁ x₂ y₁ y₂ : ZMod spec.field.modulus)
    (h₁ : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x₁ y₁)
    (h₂ : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x₂ y₂)
    (distinct :
      (.some x₁ y₁ h₁ : Point spec) ≠ (.some x₂ y₂ h₂ : Point spec))
    (notInverse :
      (.some x₁ y₁ h₁ : Point spec) ≠ -(.some x₂ y₂ h₂ : Point spec)) :
    x₁ ≠ x₂ := by
  intro sameX
  rcases (WeierstrassCurve.Affine.Point.X_eq_iff
      (W := spec.curve.toWeierstrassCurve.toAffine)).mp sameX with
    equal | inverse
  · exact distinct equal
  · exact notInverse inverse

/-- The generic-addition denominator as an explicit field unit. -/
def genericAddDenominatorUnit {width : Nat} (spec : CurveSpec width)
    (x₁ x₂ : ZMod spec.field.modulus) (distinct : x₁ ≠ x₂) :
    (ZMod spec.field.modulus)ˣ :=
  Units.mk0 (genericAddDenominator spec x₁ x₂)
    (genericAddDenominator_ne_zero spec distinct)

@[simp]
lemma genericAddDenominatorUnit_val {width : Nat} (spec : CurveSpec width)
    (x₁ x₂ : ZMod spec.field.modulus) (distinct : x₁ ≠ x₂) :
    ((genericAddDenominatorUnit spec x₁ x₂ distinct :
      (ZMod spec.field.modulus)ˣ) : ZMod spec.field.modulus) =
      genericAddDenominator spec x₁ x₂ :=
  rfl

/-- Mathlib's affine secant slope for two finite inputs. -/
def genericAddSlope {width : Nat} (spec : CurveSpec width)
    (x₁ x₂ y₁ y₂ : ZMod spec.field.modulus) : ZMod spec.field.modulus :=
  spec.curve.toWeierstrassCurve.toAffine.slope x₁ x₂ y₁ y₂

/-- The Mathlib secant slope is the conventional quotient
`(y₂ - y₁) / (x₂ - x₁)` as well. -/
lemma genericAddSlope_eq_formula {width : Nat} (spec : CurveSpec width)
    (x₁ x₂ y₁ y₂ : ZMod spec.field.modulus) (distinct : x₁ ≠ x₂) :
    genericAddSlope spec x₁ x₂ y₁ y₂ =
      genericAddNumerator spec y₁ y₂ / genericAddDenominator spec x₁ x₂ := by
  rw [genericAddSlope, WeierstrassCurve.Affine.slope_of_X_ne distinct]
  simp only [genericAddNumerator, genericAddDenominator]
  rw [show y₁ - y₂ = -(y₂ - y₁) by ring,
    show x₁ - x₂ = -(x₂ - x₁) by ring,
    neg_div_neg_eq]

/-- The short-Weierstrass `x₃ = λ² - x₁ - x₂` formula. -/
def genericAddX {width : Nat} (spec : CurveSpec width)
    (x₁ x₂ y₁ y₂ : ZMod spec.field.modulus) : ZMod spec.field.modulus :=
  genericAddSlope spec x₁ x₂ y₁ y₂ ^ 2 - x₁ - x₂

/-- The short-Weierstrass `y₃ = λ(x₁ - x₃) - y₁` formula. -/
def genericAddY {width : Nat} (spec : CurveSpec width)
    (x₁ x₂ y₁ y₂ : ZMod spec.field.modulus) : ZMod spec.field.modulus :=
  genericAddSlope spec x₁ x₂ y₁ y₂ *
      (x₁ - genericAddX spec x₁ x₂ y₁ y₂) - y₁

/-- The local generic `x₃` formula is Mathlib's affine `addX` formula for a
short-Weierstrass curve. -/
lemma genericAddX_eq_mathlib {width : Nat} (spec : CurveSpec width)
    (x₁ x₂ y₁ y₂ : ZMod spec.field.modulus) :
    genericAddX spec x₁ x₂ y₁ y₂ =
      spec.curve.toWeierstrassCurve.toAffine.addX x₁ x₂
        (genericAddSlope spec x₁ x₂ y₁ y₂) := by
  simp [genericAddX,
    QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.toWeierstrassCurve,
    WeierstrassCurve.Affine.addX]

/-- The local generic `y₃` formula is Mathlib's affine `addY` formula for a
short-Weierstrass curve. -/
lemma genericAddY_eq_mathlib {width : Nat} (spec : CurveSpec width)
    (x₁ x₂ y₁ y₂ : ZMod spec.field.modulus) :
    genericAddY spec x₁ x₂ y₁ y₂ =
      spec.curve.toWeierstrassCurve.toAffine.addY x₁ x₂ y₁
        (genericAddSlope spec x₁ x₂ y₁ y₂) := by
  simp [genericAddY, genericAddX,
    QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.toWeierstrassCurve,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY]
  ring

/-- The generic short-form coordinate pair is nonsingular whenever the two
input finite points have distinct `x` coordinates. -/
lemma genericAdd_nonsingular {width : Nat} (spec : CurveSpec width)
    (x₁ x₂ y₁ y₂ : ZMod spec.field.modulus)
    (h₁ : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x₁ y₁)
    (h₂ : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x₂ y₂)
    (distinct : x₁ ≠ x₂) :
    spec.curve.toWeierstrassCurve.toAffine.Nonsingular
      (genericAddX spec x₁ x₂ y₁ y₂) (genericAddY spec x₁ x₂ y₁ y₂) := by
  rw [genericAddX_eq_mathlib, genericAddY_eq_mathlib]
  exact WeierstrassCurve.Affine.nonsingular_add
    (W := spec.curve.toWeierstrassCurve.toAffine)
    h₁ h₂ (fun sameXAndVertical => distinct sameXAndVertical.1)

/-- Package the generic coordinate formula as the existing Mathlib point
carrier. -/
def genericAddPoint {width : Nat} (spec : CurveSpec width)
    (x₁ x₂ y₁ y₂ : ZMod spec.field.modulus)
    (h₁ : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x₁ y₁)
    (h₂ : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x₂ y₂)
    (distinct : x₁ ≠ x₂) : Point spec :=
  .some (genericAddX spec x₁ x₂ y₁ y₂)
    (genericAddY spec x₁ x₂ y₁ y₂)
    (genericAdd_nonsingular spec x₁ x₂ y₁ y₂ h₁ h₂ distinct)

/-- Generic short-form coordinates compute the same point as Mathlib affine
addition. -/
lemma genericAddPoint_eq_mathlib_add {width : Nat} (spec : CurveSpec width)
    (x₁ x₂ y₁ y₂ : ZMod spec.field.modulus)
    (h₁ : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x₁ y₁)
    (h₂ : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x₂ y₂)
    (distinct : x₁ ≠ x₂) :
    genericAddPoint spec x₁ x₂ y₁ y₂ h₁ h₂ distinct =
      Add.eval spec (.some x₁ y₁ h₁ : Point spec) (.some x₂ y₂ h₂ : Point spec) := by
  symm
  simpa [Add.eval, genericAddPoint, genericAddX_eq_mathlib,
    genericAddY_eq_mathlib, genericAddSlope] using
    WeierstrassCurve.Affine.Point.add_of_X_ne
      (W := spec.curve.toWeierstrassCurve.toAffine)
      (h₁ := h₁) (h₂ := h₂) distinct

/-- The tangent numerator `3x² + a` for a short-Weierstrass point. -/
def doubleNumerator {width : Nat} (spec : CurveSpec width)
    (x : ZMod spec.field.modulus) : ZMod spec.field.modulus :=
  (3 : ZMod spec.field.modulus) * x ^ 2 + spec.curve.a

/-- The tangent denominator `2y` for a short-Weierstrass point. -/
def doubleDenominator {width : Nat} (spec : CurveSpec width)
    (y : ZMod spec.field.modulus) : ZMod spec.field.modulus :=
  (2 : ZMod spec.field.modulus) * y

/-- Characteristic two is excluded by the curve specification. -/
lemma two_ne_zero {width : Nat} (spec : CurveSpec width) :
    (2 : ZMod spec.field.modulus) ≠ 0 := by
  intro twoZero
  have divides : spec.field.modulus ∣ 2 :=
    (ZMod.natCast_eq_zero_iff 2 spec.field.modulus).mp twoZero
  have leTwo : spec.field.modulus ≤ 2 :=
    Nat.le_of_dvd (by omega) divides
  have threeLt : 3 < spec.field.modulus := spec.curve.three_lt
  omega

/-- A nonzero finite `y` coordinate makes the tangent denominator nonzero. -/
lemma doubleDenominator_ne_zero {width : Nat} (spec : CurveSpec width)
    (y : ZMod spec.field.modulus) (nonzero : y ≠ 0) :
    doubleDenominator spec y ≠ 0 := by
  exact mul_ne_zero (two_ne_zero spec) nonzero

/-- In the prime field, the nonvertical tangent denominator is a unit. -/
lemma doubleDenominator_isUnit {width : Nat} (spec : CurveSpec width)
    (y : ZMod spec.field.modulus) (nonzero : y ≠ 0) :
    IsUnit (doubleDenominator spec y) :=
  isUnit_iff_ne_zero.mpr (doubleDenominator_ne_zero spec y nonzero)

/-- A finite point selected by the nonvertical doubling branch has nonzero
`y`: when `y = 0`, short-Weierstrass negation fixes the point. -/
lemma doubleFinite_y_ne_zero {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus)
    (h : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x y)
    (notInverse :
      (.some x y h : Point spec) ≠ -(.some x y h : Point spec)) :
    y ≠ 0 := by
  intro yZero
  apply notInverse
  subst y
  rw [WeierstrassCurve.Affine.Point.neg_some]
  simp only [WeierstrassCurve.Affine.Point.some.injEq, true_and]
  rw [mathlib_negY_eq_negY]
  simp [negY]

/-- The nonvertical tangent denominator as an explicit field unit. -/
def doubleDenominatorUnit {width : Nat} (spec : CurveSpec width)
    (y : ZMod spec.field.modulus) (nonzero : y ≠ 0) :
    (ZMod spec.field.modulus)ˣ :=
  Units.mk0 (doubleDenominator spec y)
    (doubleDenominator_ne_zero spec y nonzero)

@[simp]
lemma doubleDenominatorUnit_val {width : Nat} (spec : CurveSpec width)
    (y : ZMod spec.field.modulus) (nonzero : y ≠ 0) :
    ((doubleDenominatorUnit spec y nonzero :
      (ZMod spec.field.modulus)ˣ) : ZMod spec.field.modulus) =
      doubleDenominator spec y :=
  rfl

/-- A nonzero short-form `y` coordinate is not Mathlib's negated `y`
coordinate, so the tangent is not vertical. -/
lemma y_ne_mathlib_negY_of_ne_zero {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus) (nonzero : y ≠ 0) :
    y ≠ spec.curve.toWeierstrassCurve.toAffine.negY x y := by
  intro equalsNegY
  have yNeg : y = -y := by
    simpa [negY] using equalsNegY.trans (mathlib_negY_eq_negY spec x y)
  apply doubleDenominator_ne_zero spec y nonzero
  calc
    doubleDenominator spec y = y + y := by
      simp [doubleDenominator]
      ring
    _ = y + -y := by
      nth_rewrite 2 [yNeg]
      rfl
    _ = 0 := by simp

/-- Mathlib's nonvertical tangent slope for a finite point. -/
def doubleSlope {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus) : ZMod spec.field.modulus :=
  spec.curve.toWeierstrassCurve.toAffine.slope x x y y

/-- The Mathlib tangent slope is `(3x² + a) / (2y)` in short form. -/
lemma doubleSlope_eq_formula {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus) (nonzero : y ≠ 0) :
    doubleSlope spec x y =
      doubleNumerator spec x / doubleDenominator spec y := by
  rw [doubleSlope,
    WeierstrassCurve.Affine.slope_of_Y_ne
      (W := spec.curve.toWeierstrassCurve.toAffine)
      (x₁ := x) (x₂ := x) (y₁ := y) (y₂ := y) rfl
      (y_ne_mathlib_negY_of_ne_zero spec x y nonzero)]
  simp [doubleNumerator, doubleDenominator,
    QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.toWeierstrassCurve,
    WeierstrassCurve.Affine.negY]
  ring

/-- The short-Weierstrass doubling `x₃ = λ² - x - x` formula. -/
def doubleX {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus) : ZMod spec.field.modulus :=
  doubleSlope spec x y ^ 2 - x - x

/-- The short-Weierstrass doubling `y₃ = λ(x - x₃) - y` formula. -/
def doubleY {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus) : ZMod spec.field.modulus :=
  doubleSlope spec x y * (x - doubleX spec x y) - y

/-- The local doubling `x₃` formula is Mathlib's affine `addX` formula. -/
lemma doubleX_eq_mathlib {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus) :
    doubleX spec x y =
      spec.curve.toWeierstrassCurve.toAffine.addX x x (doubleSlope spec x y) := by
  simp [doubleX,
    QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.toWeierstrassCurve,
    WeierstrassCurve.Affine.addX]

/-- The local doubling `y₃` formula is Mathlib's affine `addY` formula. -/
lemma doubleY_eq_mathlib {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus) :
    doubleY spec x y =
      spec.curve.toWeierstrassCurve.toAffine.addY x x y (doubleSlope spec x y) := by
  simp [doubleY, doubleX,
    QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.toWeierstrassCurve,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY]
  ring

/-- The nonvertical short-form tangent coordinates are nonsingular. -/
lemma double_nonsingular {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus)
    (h : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x y)
    (nonzero : y ≠ 0) :
    spec.curve.toWeierstrassCurve.toAffine.Nonsingular
      (doubleX spec x y) (doubleY spec x y) := by
  rw [doubleX_eq_mathlib, doubleY_eq_mathlib]
  exact WeierstrassCurve.Affine.nonsingular_add
    (W := spec.curve.toWeierstrassCurve.toAffine)
    h h (fun sameXAndVertical =>
      y_ne_mathlib_negY_of_ne_zero spec x y nonzero sameXAndVertical.2)

/-- Package nonvertical short-form doubling coordinates as the existing
Mathlib point carrier. -/
def doublePoint {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus)
    (h : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x y)
    (nonzero : y ≠ 0) : Point spec :=
  .some (doubleX spec x y) (doubleY spec x y)
    (double_nonsingular spec x y h nonzero)

/-- Nonvertical short-form doubling computes the same point as Mathlib's
affine group law. -/
lemma doublePoint_eq_mathlib_double {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus)
    (h : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x y)
    (nonzero : y ≠ 0) :
    doublePoint spec x y h nonzero =
      Double.eval spec (.some x y h : Point spec) := by
  symm
  simpa [Double.eval, Add.eval, doublePoint, doubleX_eq_mathlib,
    doubleY_eq_mathlib, doubleSlope] using
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne
      (W := spec.curve.toWeierstrassCurve.toAffine)
      (h₁ := h) (y_ne_mathlib_negY_of_ne_zero spec x y nonzero)

/-- A finite point with `y = 0` has a vertical tangent and doubles to the
unique point at infinity. -/
lemma double_eval_eq_infinity_of_y_eq_zero {width : Nat}
    (spec : CurveSpec width) (x : ZMod spec.field.modulus)
    (h : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x 0) :
    Double.eval spec (.some x 0 h : Point spec) = Point.infinity spec := by
  change (.some x 0 h : Point spec) + .some x 0 h = 0
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  simp [QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.toWeierstrassCurve,
    WeierstrassCurve.Affine.negY]

end

end ShortWeierstrass
end EllipticCurve

end ClassicalAlgorithms
end QuantumAlg

end
