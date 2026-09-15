/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Generic.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Affine.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Selected

/-!
# Original point addition from the actual selected generic output

The actual two subtractions materialize the original secant numerator and
denominator. The original branch decision supplies their unit condition and
the affine exclusions. The common actual tail therefore returns the original
point sum in the original nominal encoding.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve
open ClassicalAlgorithms.EllipticCurve.ShortWeierstrass Field.Native

noncomputable section

variable {width : Nat}

/-- The selected generic branch's actual finite output represents the original point sum. -/
theorem genericOutputValue_represents_add_of_selected (spec : CurveSpec width)
    (left right : CShape.Value (PointEquality.RawPointShape width))
    (x₁ x₂ y₁ y₂ : ZMod spec.field.modulus)
    (h₁ : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x₁ y₁)
    (h₂ : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x₂ y₂)
    (leftXValue : left.second.first.toNat = x₁.val)
    (rightXValue : right.second.first.toNat = x₂.val)
    (leftYValue : left.second.second.toNat = y₁.val)
    (rightYValue : right.second.second.toNat = y₂.val)
    (selected : ClassicalAlgorithms.EllipticCurve.Add.branch spec
      (.some x₁ y₁ h₁) (.some x₂ y₂ h₂) = .generic) :
    PointRepresents spec (genericOutputValue spec.field left right)
      (ClassicalAlgorithms.EllipticCurve.Add.eval spec (.some x₁ y₁ h₁) (.some x₂ y₂ h₂)) := by
  have conditions := generic_conditions_of_selected spec _ _ selected
  have distinct := genericFinite_x_ne spec x₁ x₂ y₁ y₂ h₁ h₂
    conditions.2.2.2 conditions.2.2.1
  have unit := generic_denominator_isUnit_of_selected spec _ _ x₁ x₂ y₁ y₂ h₁ h₂
    rfl rfl selected
  have leftXCanonical : left.second.first.toNat < spec.field.modulus := by
    rw [leftXValue]
    exact ZMod.val_lt x₁
  have rightXCanonical : right.second.first.toNat < spec.field.modulus := by
    rw [rightXValue]
    exact ZMod.val_lt x₂
  have leftYCanonical : left.second.second.toNat < spec.field.modulus := by
    rw [leftYValue]
    exact ZMod.val_lt y₁
  let numerator := subtractionWord spec.field right.second.second left.second.second
  let denominator := subtractionWord spec.field right.second.first left.second.first
  have numeratorCanonical : numerator.toNat < spec.field.modulus :=
    subtractionWord_canonical spec.field _ _ leftYCanonical
  have denominatorCanonical : denominator.toNat < spec.field.modulus :=
    subtractionWord_canonical spec.field _ _ leftXCanonical
  have numeratorCast : (numerator.toNat : ZMod spec.field.modulus) =
      genericAddNumerator spec y₁ y₂ := by
    rw [subtractionWord_cast spec.field _ _ leftYCanonical, rightYValue, leftYValue,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rfl
  have denominatorCast : (denominator.toNat : ZMod spec.field.modulus) =
      genericAddDenominator spec x₁ x₂ := by
    rw [subtractionWord_cast spec.field _ _ leftXCanonical, rightXValue, leftXValue,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rfl
  have numeratorValue : numerator.toNat = (genericAddNumerator spec y₁ y₂).val := by
    have value := congrArg ZMod.val numeratorCast
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt numeratorCanonical] using value
  have denominatorValue : denominator.toNat = (genericAddDenominator spec x₁ x₂).val := by
    have value := congrArg ZMod.val denominatorCast
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt denominatorCanonical] using value
  let values := affineValues spec.field left.second.first right.second.first left.second.second
    numerator denominator
  have canonical := affineValues_output_canonical spec.field left.second.first right.second.first
    left.second.second numerator denominator rightXCanonical leftYCanonical
  have formulas := affineValues_field_coordinates spec.field left.second.first right.second.first
    left.second.second numerator denominator x₁ x₂ y₁ (genericAddNumerator spec y₁ y₂)
    (genericAddDenominator spec x₁ x₂) leftXValue rightXValue leftYValue numeratorValue
    denominatorValue unit
  have xValue : (values.xOutput.toNat : ZMod spec.field.modulus) =
      genericAddX spec x₁ x₂ y₁ y₂ := by
    simpa only [genericAddX, genericAddSlope_eq_formula spec x₁ x₂ y₁ y₂ distinct, div_eq_mul_inv]
      using formulas.2.1
  have yValue : (values.yOutput.toNat : ZMod spec.field.modulus) =
      genericAddY spec x₁ x₂ y₁ y₂ := by
    simpa only [genericAddY, genericAddX, genericAddSlope_eq_formula spec x₁ x₂ y₁ y₂ distinct,
      div_eq_mul_inv] using formulas.2.2
  have represented := AffineValues.point_represents spec values
    (genericAddX spec x₁ x₂ y₁ y₂) (genericAddY spec x₁ x₂ y₁ y₂)
    (genericAdd_nonsingular spec x₁ x₂ y₁ y₂ h₁ h₂ distinct)
    canonical.1 canonical.2 xValue yValue
  change PointRepresents spec (values.point (.bit false))
    (ClassicalAlgorithms.EllipticCurve.Add.eval spec (.some x₁ y₁ h₁) (.some x₂ y₂ h₂))
  rw [← genericAddPoint_eq_mathlib_add spec x₁ x₂ y₁ y₂ h₁ h₂ distinct]
  exact represented

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
