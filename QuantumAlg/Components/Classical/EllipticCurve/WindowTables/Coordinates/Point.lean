/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Values
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Domain

/-!
# Canonical coordinate words representing the original group point

This invariant records the original actual coordinate words, their
canonical representatives and the existing affine group point. Doubling
uses the already proved finite-word expressions and the original nonzero
tangent domain. It introduces no executable mathematical inverse.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {width : Nat}

/-- Canonical actual coordinate words representing one nonsingular original finite point. -/
structure CoordinateValue (spec : CurveSpec width) (x y : CShape.Word width)
    (point : Point spec) : Prop where
  xCanonical : x.toNat < spec.field.modulus
  yCanonical : y.toNat < spec.field.modulus
  finite : spec.curve.toWeierstrassCurve.toAffine.Nonsingular
    (x.toNat : ZMod spec.field.modulus) (y.toNat : ZMod spec.field.modulus)
  represents : (.some (x.toNat : ZMod spec.field.modulus)
    (y.toNat : ZMod spec.field.modulus) finite : Point spec) = point

/-- The original paid finite-word doubling expressions represent the original doubled point. -/
lemma CoordinateValue.doubleWords_value (spec : CurveSpec width)
    (x y curveA : CShape.Word width) (point : Point spec)
    (value : CoordinateValue spec x y point)
    (curveValue : (curveA.toNat : ZMod spec.field.modulus) = spec.curve.a)
    (doubled : point + point ≠ 0) :
    CoordinateValue spec (doubleWords spec.field x y curveA).1
      (doubleWords spec.field x y curveA).2 (point + point) := by
  have yNonzero : (y.toNat : ZMod spec.field.modulus) ≠ 0 :=
    finite_y_ne_zero_of_double_ne_zero spec _ _ value.finite (by
      rw [value.represents]
      exact doubled)
  have slope :
      (3 * (x.toNat : ZMod spec.field.modulus) ^ 2 + curveA.toNat) *
        ((2 : ZMod spec.field.modulus) * y.toNat)⁻¹ =
      ShortWeierstrass.doubleSlope spec x.toNat y.toNat := by
    rw [ShortWeierstrass.doubleSlope_eq_formula spec _ _ yNonzero]
    simp only [ShortWeierstrass.doubleNumerator, ShortWeierstrass.doubleDenominator,
      div_eq_mul_inv]
    rw [curveValue]
  have casts := doubleWords_cast spec.field x y curveA value.yCanonical
    (mul_ne_zero (ShortWeierstrass.two_ne_zero spec) yNonzero)
  dsimp only at casts
  rw [slope] at casts
  have coordinates :
      ((doubleWords spec.field x y curveA).1.toNat : ZMod spec.field.modulus) =
        ShortWeierstrass.doubleX spec x.toNat y.toNat ∧
      ((doubleWords spec.field x y curveA).2.toNat : ZMod spec.field.modulus) =
        ShortWeierstrass.doubleY spec x.toNat y.toNat := casts
  have finite : spec.curve.toWeierstrassCurve.toAffine.Nonsingular
      ((doubleWords spec.field x y curveA).1.toNat : ZMod spec.field.modulus)
      ((doubleWords spec.field x y curveA).2.toNat : ZMod spec.field.modulus) := by
    rw [coordinates.1, coordinates.2]
    exact ShortWeierstrass.double_nonsingular spec _ _ value.finite yNonzero
  refine ⟨(doubleWords_canonical spec.field x y curveA value.yCanonical).1,
    (doubleWords_canonical spec.field x y curveA value.yCanonical).2, finite, ?_⟩
  calc
    (.some _ _ finite : Point spec) =
        ShortWeierstrass.doublePoint spec x.toNat y.toNat value.finite yNonzero := by
      simp only [ShortWeierstrass.doublePoint, WeierstrassCurve.Affine.Point.some.injEq]
      exact coordinates
    _ = Double.eval spec (.some _ _ value.finite : Point spec) :=
      ShortWeierstrass.doublePoint_eq_mathlib_double spec _ _ value.finite yNonzero
    _ = point + point := by
      change (.some _ _ value.finite : Point spec) + .some _ _ value.finite = _
      rw [value.represents]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
