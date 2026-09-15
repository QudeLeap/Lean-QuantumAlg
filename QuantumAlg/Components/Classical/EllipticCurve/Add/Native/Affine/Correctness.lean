/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Affine.Values
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Coefficient.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Word.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.Representation.Model

/-!
# Original field coordinates from the actual common affine-tail words

The actual total coefficient and finite-word arithmetic retain their exact
outputs. Canonical coordinate inputs and a local unit denominator identify
those same outputs with the original slope and affine coordinate formulas.
Canonical final coordinates, their exact field values and nonsingularity
then certify the original nominal point encoding. No output point or inverse
is supplied to the executable computation.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve Field.Native

noncomputable section

variable {width : Nat}

/-- The two final actual words are canonical on the original coordinate domains. -/
theorem affineValues_output_canonical (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CShape.Word width)
    (rightXCanonical : rightX.toNat < spec.modulus)
    (leftYCanonical : leftY.toNat < spec.modulus) :
    (affineValues spec leftX rightX leftY numerator denominator).xOutput.toNat < spec.modulus ∧
      (affineValues spec leftX rightX leftY numerator denominator).yOutput.toNat < spec.modulus :=
  ⟨subtractionWord_canonical spec _ rightX rightXCanonical,
    subtractionWord_canonical spec _ leftY leftYCanonical⟩

/-- The actual coefficient and all subsequent words give the original three field formulas. -/
theorem affineValues_field_coordinates (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CShape.Word width)
    (x₁ x₂ y₁ ν δ : ZMod spec.modulus)
    (leftXValue : leftX.toNat = x₁.val) (rightXValue : rightX.toNat = x₂.val)
    (leftYValue : leftY.toNat = y₁.val) (numeratorValue : numerator.toNat = ν.val)
    (denominatorValue : denominator.toNat = δ.val) (unit : IsUnit δ) :
    let values := affineValues spec leftX rightX leftY numerator denominator
    (values.slope.toNat : ZMod spec.modulus) = ν * δ⁻¹ ∧
      (values.xOutput.toNat : ZMod spec.modulus) = (ν * δ⁻¹) ^ 2 - x₁ - x₂ ∧
      (values.yOutput.toNat : ZMod spec.modulus) =
        (ν * δ⁻¹) * (x₁ - ((ν * δ⁻¹) ^ 2 - x₁ - x₂)) - y₁ := by
  let _ : NeZero spec.modulus := ⟨Nat.ne_of_gt (modulusSpec_modulus_pos spec)⟩
  let values := affineValues spec leftX rightX leftY numerator denominator
  have leftXCanonical : leftX.toNat < spec.modulus := by
    rw [leftXValue]
    exact ZMod.val_lt x₁
  have rightXCanonical : rightX.toNat < spec.modulus := by
    rw [rightXValue]
    exact ZMod.val_lt x₂
  have leftYCanonical : leftY.toNat < spec.modulus := by
    rw [leftYValue]
    exact ZMod.val_lt y₁
  have leftXCast : (leftX.toNat : ZMod spec.modulus) = x₁ := by
    rw [leftXValue, ZMod.natCast_zmod_val]
  have rightXCast : (rightX.toNat : ZMod spec.modulus) = x₂ := by
    rw [rightXValue, ZMod.natCast_zmod_val]
  have leftYCast : (leftY.toNat : ZMod spec.modulus) = y₁ := by
    rw [leftYValue, ZMod.natCast_zmod_val]
  have numeratorCast : (numerator.toNat : ZMod spec.modulus) = ν := by
    rw [numeratorValue, ZMod.natCast_zmod_val]
  have coefficientNat : values.coefficient.toNat = (coefficientResidue spec denominator).val := by
    change (coefficientResidue spec denominator).val % 2 ^ width = _
    exact Nat.mod_eq_of_lt ((coefficientResidue spec denominator).isLt.trans_le spec.le_capacity)
  have coefficientCast : (values.coefficient.toNat : ZMod spec.modulus) = δ⁻¹ := by
    rw [coefficientNat]
    exact coefficientResidue_cast_eq_inv spec denominator δ denominatorValue unit
  have slope : (values.slope.toNat : ZMod spec.modulus) = ν * δ⁻¹ := by
    change ((CShape.wordOfNat width
      (numerator.toNat * values.coefficient.toNat % spec.modulus)).toNat : ZMod spec.modulus) = _
    rw [fieldMulWord_cast, numeratorCast, coefficientCast]
  have squared : (values.slopeSquared.toNat : ZMod spec.modulus) = (ν * δ⁻¹) ^ 2 := by
    change ((CShape.wordOfNat width
      (values.slope.toNat * values.slope.toNat % spec.modulus)).toNat : ZMod spec.modulus) = _
    rw [fieldMulWord_cast, slope, pow_two]
  have partialX : (values.xPartial.toNat : ZMod spec.modulus) = (ν * δ⁻¹) ^ 2 - x₁ := by
    change ((subtractionWord spec values.slopeSquared leftX).toNat : ZMod spec.modulus) = _
    rw [subtractionWord_cast spec _ _ leftXCanonical, squared, leftXCast]
  have outputX : (values.xOutput.toNat : ZMod spec.modulus) = (ν * δ⁻¹) ^ 2 - x₁ - x₂ := by
    change ((subtractionWord spec values.xPartial rightX).toNat : ZMod spec.modulus) = _
    rw [subtractionWord_cast spec _ _ rightXCanonical, partialX, rightXCast]
  have outputCanonical := affineValues_output_canonical spec leftX rightX leftY numerator
    denominator rightXCanonical leftYCanonical
  have difference : (values.xDifference.toNat : ZMod spec.modulus) =
      x₁ - ((ν * δ⁻¹) ^ 2 - x₁ - x₂) := by
    change ((subtractionWord spec leftX values.xOutput).toNat : ZMod spec.modulus) = _
    rw [subtractionWord_cast spec _ _ outputCanonical.1, leftXCast, outputX]
  have product : (values.yProduct.toNat : ZMod spec.modulus) =
      (ν * δ⁻¹) * (x₁ - ((ν * δ⁻¹) ^ 2 - x₁ - x₂)) := by
    change ((CShape.wordOfNat width
      (values.slope.toNat * values.xDifference.toNat % spec.modulus)).toNat : ZMod spec.modulus) = _
    rw [fieldMulWord_cast, slope, difference]
  refine ⟨slope, outputX, ?_⟩
  change ((subtractionWord spec values.yProduct leftY).toNat : ZMod spec.modulus) = _
  rw [subtractionWord_cast spec _ _ leftYCanonical, product, leftYCast]

private theorem canonical_word_eq_coordinate (spec : CurveSpec width)
    (word : CShape.Word width) (coordinate : ZMod spec.field.modulus)
    (canonical : word.toNat < spec.field.modulus)
    (represented : (word.toNat : ZMod spec.field.modulus) = coordinate) :
    word = .unsignedWord (ClassicalAlgorithms.EllipticCurve.coordinateWord spec coordinate) := by
  cases word with
  | unsignedWord bits =>
    apply congrArg CShape.Value.unsignedWord
    apply Fin.ext
    have value := congrArg ZMod.val represented
    have bitsCanonical : bits.val < spec.field.modulus := canonical
    rw [ZMod.val_natCast] at value
    change bits.val % spec.field.modulus = coordinate.val at value
    rw [Nat.mod_eq_of_lt bitsCanonical] at value
    exact value

/-- Actual canonical packed coordinates represent exactly the supplied nonsingular finite point. -/
theorem AffineValues.point_represents (spec : CurveSpec width) (values : AffineValues width)
    (x y : ZMod spec.field.modulus)
    (nonsingular : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x y)
    (xCanonical : values.xOutput.toNat < spec.field.modulus)
    (yCanonical : values.yOutput.toNat < spec.field.modulus)
    (xValue : (values.xOutput.toNat : ZMod spec.field.modulus) = x)
    (yValue : (values.yOutput.toNat : ZMod spec.field.modulus) = y) :
    PointRepresents spec (values.point (.bit false)) (.some x y nonsingular) := by
  have xWord := canonical_word_eq_coordinate spec values.xOutput x xCanonical xValue
  have yWord := canonical_word_eq_coordinate spec values.yOutput y yCanonical yValue
  have encoded : values.point (.bit false) = encodePoint spec (.some x y nonsingular) := by
    rw [AffineValues.point, xWord, yWord]
    rfl
  rw [encoded]
  exact encodePoint_represents spec (.some x y nonsingular)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
