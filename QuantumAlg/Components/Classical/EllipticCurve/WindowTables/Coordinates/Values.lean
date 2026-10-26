/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Words

/-!
# Field interpretation of the original finite-word doubling expressions

The actual total coefficient word becomes the denominator's field inverse
on its original canonical nonzero domain. Every subsequent finite-word
multiply, addition and canonical-right subtraction then gives the original
affine formulas. No inverse operation is inserted into executable code.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open ClassicalAlgorithms.Modular Modular.NativePower Field.Native.Shared

noncomputable section

variable {width : Nat}

/-- Original finite-word expressions give the original affine doubling formulas. -/
lemma doubleWords_cast (spec : ModulusSpec width) [Fact spec.modulus.Prime]
    (x y curveA : CShape.Word width) (yCanonical : y.toNat < spec.modulus)
    (nonzero : (2 : ZMod spec.modulus) * y.toNat ≠ 0) :
    let slope : ZMod spec.modulus :=
      (3 * (x.toNat : ZMod spec.modulus) ^ 2 + curveA.toNat) *
        ((2 : ZMod spec.modulus) * y.toNat)⁻¹
    let nextX := slope ^ 2 - x.toNat - x.toNat
    ((doubleWords spec x y curveA).1.toNat : ZMod spec.modulus) = nextX ∧
      ((doubleWords spec x y curveA).2.toNat : ZMod spec.modulus) =
        slope * (x.toNat - nextX) - y.toNat := by
  let modulus : CShape.Word (width + 1) := .unsignedWord spec.extendedWord
  let denominator := addValue y y modulus
  let inverse := coefficientWordValue spec denominator
  let square := multiplyValue x x modulus
  let numerator := addValue (addValue (addValue square square modulus) square modulus)
    curveA modulus
  let slopeWord := multiplyValue numerator inverse modulus
  let nextXWord := subValue (multiplyValue slopeWord slopeWord modulus)
    (addValue x x modulus) modulus
  let nextYWord := subValue
    (multiplyValue slopeWord (subValue x nextXWord modulus) modulus) y modulus
  let slopeField : ZMod spec.modulus :=
    (3 * (x.toNat : ZMod spec.modulus) ^ 2 + curveA.toNat) *
      ((2 : ZMod spec.modulus) * y.toNat)⁻¹
  have denominatorCast : (denominator.toNat : ZMod spec.modulus) =
      (2 : ZMod spec.modulus) * y.toNat := by
    dsimp only [denominator, modulus]
    rw [addValue_cast]
    ring
  have denominatorCanonical : denominator.toNat < spec.modulus :=
    addValue_canonical spec _ _
  have inverseCast : (inverse.toNat : ZMod spec.modulus) =
      ((2 : ZMod spec.modulus) * y.toNat)⁻¹ := by
    have actual := coefficientWordValue_cast_eq_inv spec denominator denominatorCanonical
      (by rw [denominatorCast]; exact nonzero)
    exact actual.trans (congrArg Inv.inv denominatorCast)
  have numeratorCast : (numerator.toNat : ZMod spec.modulus) =
      3 * (x.toNat : ZMod spec.modulus) ^ 2 + curveA.toNat := by
    dsimp only [numerator, square, modulus]
    simp only [addValue_cast, multiplyValue_cast]
    ring
  have slopeCast : (slopeWord.toNat : ZMod spec.modulus) = slopeField := by
    change ((multiplyValue numerator inverse (.unsignedWord spec.extendedWord)).toNat :
      ZMod spec.modulus) = slopeField
    rw [multiplyValue_cast, numeratorCast, inverseCast]
  have nextXCanonical : nextXWord.toNat < spec.modulus :=
    subValue_canonical spec _ _ (addValue_canonical spec _ _)
  have nextXCast : (nextXWord.toNat : ZMod spec.modulus) =
      slopeField ^ 2 - x.toNat - x.toNat := by
    change ((subValue (multiplyValue slopeWord slopeWord (.unsignedWord spec.extendedWord))
      (addValue x x (.unsignedWord spec.extendedWord))
      (.unsignedWord spec.extendedWord)).toNat : ZMod spec.modulus) = _
    rw [subValue_cast spec _ _ (addValue_canonical spec _ _), multiplyValue_cast, addValue_cast]
    simp only [slopeCast]
    ring
  have nextYCast : (nextYWord.toNat : ZMod spec.modulus) =
      slopeField * (x.toNat - (slopeField ^ 2 - x.toNat - x.toNat)) - y.toNat := by
    change ((subValue (multiplyValue slopeWord
      (subValue x nextXWord (.unsignedWord spec.extendedWord))
      (.unsignedWord spec.extendedWord)) y (.unsignedWord spec.extendedWord)).toNat :
      ZMod spec.modulus) = _
    rw [subValue_cast spec _ _ yCanonical, multiplyValue_cast,
      subValue_cast spec x nextXWord nextXCanonical, slopeCast, nextXCast]
  exact ⟨nextXCast, nextYCast⟩

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
