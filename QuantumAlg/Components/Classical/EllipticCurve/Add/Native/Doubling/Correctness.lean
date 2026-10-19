/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Doubling.Values
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Affine.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Selected

/-!
# Original point doubling from the actual selected tangent output

The original materialized square, two additions, loaded curve coefficient,
numerator and denominator retain their finite-word values. The original
selected branch supplies the nonvertical tangent condition. The actual common
tail then returns the original point sum in its original nominal encoding.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve
open ClassicalAlgorithms.EllipticCurve.ShortWeierstrass Field.Native

noncomputable section

variable {width : Nat}

/-- The six actual prefix values give the original canonical tangent numerator and denominator. -/
lemma doublingValues_slope_operands (spec : CurveSpec width)
    (rawX rawY : CShape.Word width) (x y : ZMod spec.field.modulus)
    (xValue : rawX.toNat = x.val) (yValue : rawY.toNat = y.val) :
    (doublingValues spec rawX rawY).numerator.toNat = (doubleNumerator spec x).val ∧
      (doublingValues spec rawX rawY).denominator.toNat = (doubleDenominator spec y).val := by
  let values := doublingValues spec rawX rawY
  have xCast : (rawX.toNat : ZMod spec.field.modulus) = x := by
    rw [xValue, ZMod.natCast_zmod_val]
  have yCast : (rawY.toNat : ZMod spec.field.modulus) = y := by
    rw [yValue, ZMod.natCast_zmod_val]
  have aValue : values.a.toNat = spec.curve.a.val := by
    change spec.curve.a.val % 2 ^ width = spec.curve.a.val
    exact Nat.mod_eq_of_lt ((ZMod.val_lt spec.curve.a).trans_le spec.field.le_capacity)
  have aCast : (values.a.toNat : ZMod spec.field.modulus) = spec.curve.a := by
    rw [aValue, ZMod.natCast_zmod_val]
  have squared : (values.xSquared.toNat : ZMod spec.field.modulus) = x ^ 2 := by
    change ((CShape.wordOfNat width (rawX.toNat * rawX.toNat % spec.field.modulus)).toNat :
      ZMod spec.field.modulus) = _
    rw [fieldMulWord_cast, xCast, pow_two]
  have doubled : (values.doubledXSquared.toNat : ZMod spec.field.modulus) = x ^ 2 + x ^ 2 := by
    change ((CShape.wordOfNat width
      ((values.xSquared.toNat + values.xSquared.toNat) % spec.field.modulus)).toNat :
        ZMod spec.field.modulus) = _
    rw [fieldAddWord_cast, squared]
  have tripled : (values.tripledXSquared.toNat : ZMod spec.field.modulus) =
      x ^ 2 + x ^ 2 + x ^ 2 := by
    change ((CShape.wordOfNat width
      ((values.doubledXSquared.toNat + values.xSquared.toNat) % spec.field.modulus)).toNat :
        ZMod spec.field.modulus) = _
    rw [fieldAddWord_cast, doubled, squared]
  have numeratorCast : (values.numerator.toNat : ZMod spec.field.modulus) =
      doubleNumerator spec x := by
    change ((CShape.wordOfNat width
      ((values.tripledXSquared.toNat + values.a.toNat) % spec.field.modulus)).toNat :
        ZMod spec.field.modulus) = _
    rw [fieldAddWord_cast, tripled, aCast, doubleNumerator]
    ring
  have denominatorCast : (values.denominator.toNat : ZMod spec.field.modulus) =
      doubleDenominator spec y := by
    change ((CShape.wordOfNat width ((rawY.toNat + rawY.toNat) % spec.field.modulus)).toNat :
      ZMod spec.field.modulus) = _
    rw [fieldAddWord_cast, yCast, doubleDenominator]
    ring
  have numeratorCanonical : values.numerator.toNat < spec.field.modulus :=
    fieldAddWord_canonical spec.field values.tripledXSquared values.a
  have denominatorCanonical : values.denominator.toNat < spec.field.modulus :=
    fieldAddWord_canonical spec.field rawY rawY
  constructor
  · have value := congrArg ZMod.val numeratorCast
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt numeratorCanonical] using value
  · have value := congrArg ZMod.val denominatorCast
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt denominatorCanonical] using value

/-- The selected tangent branch's actual finite output represents the original point sum. -/
lemma doublingOutputValue_represents_add_of_selected (spec : CurveSpec width)
    (point : CShape.Value (PointEquality.RawPointShape width))
    (x y : ZMod spec.field.modulus)
    (h : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x y)
    (xValue : point.second.first.toNat = x.val)
    (yValue : point.second.second.toNat = y.val)
    (selected : ClassicalAlgorithms.EllipticCurve.Add.branch spec
      (.some x y h) (.some x y h) = .doubling) :
    PointRepresents spec (doublingOutputValue spec point)
      (ClassicalAlgorithms.EllipticCurve.Add.eval spec (.some x y h) (.some x y h)) := by
  have conditions := doubling_conditions_of_selected spec _ _ selected
  have nonzero := doubleFinite_y_ne_zero spec x y h conditions.2.2.1
  have unit := doubling_denominator_isUnit_of_selected spec _ _ x y h rfl rfl selected
  have xCanonical : point.second.first.toNat < spec.field.modulus := by
    rw [xValue]
    exact ZMod.val_lt x
  have yCanonical : point.second.second.toNat < spec.field.modulus := by
    rw [yValue]
    exact ZMod.val_lt y
  let operandsWords := doublingValues spec point.second.first point.second.second
  have operands := doublingValues_slope_operands spec point.second.first point.second.second
    x y xValue yValue
  let values := affineValues spec.field point.second.first point.second.first point.second.second
    operandsWords.numerator operandsWords.denominator
  have canonical := affineValues_output_canonical spec.field point.second.first point.second.first
    point.second.second operandsWords.numerator operandsWords.denominator
      xCanonical yCanonical
  have formulas := affineValues_field_coordinates spec.field point.second.first point.second.first
    point.second.second operandsWords.numerator operandsWords.denominator x x y
    (doubleNumerator spec x) (doubleDenominator spec y) xValue xValue yValue
    operands.1 operands.2 unit
  have outputX : (values.xOutput.toNat : ZMod spec.field.modulus) = doubleX spec x y := by
    simpa only [doubleX, doubleSlope_eq_formula spec x y nonzero, div_eq_mul_inv]
      using formulas.2.1
  have outputY : (values.yOutput.toNat : ZMod spec.field.modulus) = doubleY spec x y := by
    simpa only [doubleY, doubleX, doubleSlope_eq_formula spec x y nonzero, div_eq_mul_inv]
      using formulas.2.2
  have represented := AffineValues.point_represents spec values (doubleX spec x y)
    (doubleY spec x y) (double_nonsingular spec x y h nonzero)
    canonical.1 canonical.2 outputX outputY
  change PointRepresents spec (values.point (.bit false))
    (ClassicalAlgorithms.EllipticCurve.Double.eval spec (.some x y h))
  rw [← doublePoint_eq_mathlib_double spec x y h nonzero]
  exact represented

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
