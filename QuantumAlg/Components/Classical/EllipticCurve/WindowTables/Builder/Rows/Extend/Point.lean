/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Point
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Extend.Values

/-!
# Original affine group value of the secant finite-word expressions

The actual inverse row has its preceding batch's field value. Distinct
original coordinate x values identify the conventional nonexceptional
secant branch, and the literal finite-word outputs represent the original
group sum with canonical coordinates.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {width : Nat}

/-- The original secant finite words represent exactly the original affine group sum. -/
lemma CoordinateValue.extendWords_value (curve : CurveSpec width)
    (x y baseX baseY inverse : CShape.Word width) (point basePoint : Point curve)
    (value : CoordinateValue curve x y point)
    (baseValue : CoordinateValue curve baseX baseY basePoint)
    (distinct : (x.toNat : ZMod curve.field.modulus) ≠ baseX.toNat)
    (inverseValue : (inverse.toNat : ZMod curve.field.modulus) =
      ((baseX.toNat : ZMod curve.field.modulus) - x.toNat)⁻¹) :
    CoordinateValue curve (extendWords curve.field x y baseX baseY inverse).1
      (extendWords curve.field x y baseX baseY inverse).2 (point + basePoint) := by
  have slope :
      (baseY.toNat - (y.toNat : ZMod curve.field.modulus)) *
        ((baseX.toNat : ZMod curve.field.modulus) - x.toNat)⁻¹ =
      ShortWeierstrass.genericAddSlope curve x.toNat baseX.toNat y.toNat baseY.toNat := by
    rw [ShortWeierstrass.genericAddSlope_eq_formula curve _ _ _ _ distinct]
    simp only [ShortWeierstrass.genericAddNumerator, ShortWeierstrass.genericAddDenominator,
      div_eq_mul_inv]
  have casts := extendWords_cast curve.field x y baseX baseY inverse value.xCanonical
    value.yCanonical baseValue.xCanonical inverseValue
  dsimp only at casts
  rw [slope] at casts
  have coordinates :
      ((extendWords curve.field x y baseX baseY inverse).1.toNat : ZMod curve.field.modulus) =
        ShortWeierstrass.genericAddX curve x.toNat baseX.toNat y.toNat baseY.toNat ∧
      ((extendWords curve.field x y baseX baseY inverse).2.toNat : ZMod curve.field.modulus) =
        ShortWeierstrass.genericAddY curve x.toNat baseX.toNat y.toNat baseY.toNat := casts
  have finite : curve.curve.toWeierstrassCurve.toAffine.Nonsingular
      ((extendWords curve.field x y baseX baseY inverse).1.toNat : ZMod curve.field.modulus)
      ((extendWords curve.field x y baseX baseY inverse).2.toNat : ZMod curve.field.modulus) := by
    rw [coordinates.1, coordinates.2]
    exact ShortWeierstrass.genericAdd_nonsingular curve _ _ _ _ value.finite baseValue.finite
      distinct
  have canonical := extendWords_canonical curve.field x y baseX baseY inverse
    value.yCanonical baseValue.xCanonical
  refine ⟨canonical.1, canonical.2, finite, ?_⟩
  calc
    (.some _ _ finite : Point curve) =
        ShortWeierstrass.genericAddPoint curve x.toNat baseX.toNat y.toNat baseY.toNat
          value.finite baseValue.finite distinct := by
      simp only [ShortWeierstrass.genericAddPoint, WeierstrassCurve.Affine.Point.some.injEq]
      exact coordinates
    _ = Add.eval curve (.some _ _ value.finite : Point curve)
        (.some _ _ baseValue.finite : Point curve) :=
      ShortWeierstrass.genericAddPoint_eq_mathlib_add curve _ _ _ _ value.finite baseValue.finite
        distinct
    _ = point + basePoint := by
      change (.some _ _ value.finite : Point curve) + .some _ _ baseValue.finite = _
      rw [value.represents, baseValue.represents]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
