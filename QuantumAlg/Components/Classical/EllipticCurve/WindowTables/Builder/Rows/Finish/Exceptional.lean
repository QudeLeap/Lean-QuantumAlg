/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Finish.Values
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Domain.Exceptional

/-!
# Original exceptional-slope value of the final paid row expressions

The reused C entry is the inverse of the original negative tangent
denominator. Its actual multiply expression is therefore the negative
original exceptional secant slope. Both denominator domains follow from
the original finite point's order; no separate exceptional-value witness
is inserted into a table program or a quantum contract.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve

noncomputable section

/-- The literal fourth final word is the original negative exceptional slope. -/
lemma finishWords_exceptional_cast {width : Nat} (spec : CurveSpec width)
    (x y curveA inverse zero one : CShape.Word width)
    (xCanonical : x.toNat < spec.field.modulus) (yCanonical : y.toNat < spec.field.modulus)
    (zeroValue : zero.toNat = 0) (oneValue : one.toNat = 1)
    (curveAValue : (curveA.toNat : ZMod spec.field.modulus) = spec.curve.a)
    (finite : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x.toNat y.toNat)
    (large : 3 < addOrderOf (.some (x.toNat : ZMod spec.field.modulus) y.toNat finite : Point spec))
    (inverseValue : (inverse.toNat : ZMod spec.field.modulus) =
      (-((2 : ZMod spec.field.modulus) * y.toNat))⁻¹) :
    ((finishWords spec.field x y curveA inverse zero one 3).toNat : ZMod spec.field.modulus) =
      -exceptionalSlope spec x.toNat y.toNat := by
  have domains := window_row_denominators_of_order spec x.toNat y.toNat finite large
  have nonzeroY : (y.toNat : ZMod spec.field.modulus) ≠ 0 := by
    intro zeroY
    rw [zeroY, mul_zero, neg_zero] at domains
    exact domains.1 rfl
  have tangent := ShortWeierstrass.doubleSlope_eq_formula spec x.toNat
    (-(y.toNat : ZMod spec.field.modulus)) (neg_ne_zero.mpr nonzeroY)
  have actual := finishWords_cast spec.field x y curveA inverse zero one
    xCanonical yCanonical zeroValue oneValue 3
  change ((finishWords spec.field x y curveA inverse zero one 3).toNat :
    ZMod spec.field.modulus) =
      (3 * (x.toNat : ZMod spec.field.modulus) ^ 2 + curveA.toNat) * inverse.toNat at actual
  rw [curveAValue, inverseValue]
    at actual
  refine actual.trans ?_
  rw [negative_exceptionalSlope_eq_tangent spec x.toNat y.toNat domains.2, tangent,
    ShortWeierstrass.doubleNumerator, ShortWeierstrass.doubleDenominator, div_eq_mul_inv]
  rw [mul_neg]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
