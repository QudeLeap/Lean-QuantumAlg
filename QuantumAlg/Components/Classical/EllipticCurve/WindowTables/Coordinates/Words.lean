/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Arithmetic

/-!
# Original finite-word doubling expressions

The expressions follow the existing paid doubling slots, including their
total raw XGCD coefficient. They describe finite-word values and introduce
no runtime instruction, mathematical inverse access or table-value oracle.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open ClassicalAlgorithms.Modular Modular.NativePower Field.Native.Shared

noncomputable section

variable {width : Nat}

/-- Total original finite-word outputs of shared-modulus affine doubling. -/
def doubleWords (spec : ModulusSpec width) (x y curveA : CShape.Word width) :
    CShape.Word width × CShape.Word width :=
  let modulus : CShape.Word (width + 1) := .unsignedWord spec.extendedWord
  let denominator := addValue y y modulus
  let inverse := coefficientWordValue spec denominator
  let square := multiplyValue x x modulus
  let numerator := addValue (addValue (addValue square square modulus) square modulus)
    curveA modulus
  let slope := multiplyValue numerator inverse modulus
  let nextX := subValue (multiplyValue slope slope modulus) (addValue x x modulus) modulus
  let nextY := subValue (multiplyValue slope (subValue x nextX modulus) modulus) y modulus
  (nextX, nextY)

/-- Both original computed coordinates are canonical whenever the final right operand is. -/
lemma doubleWords_canonical (spec : ModulusSpec width) (x y curveA : CShape.Word width)
    (yCanonical : y.toNat < spec.modulus) :
    (doubleWords spec x y curveA).1.toNat < spec.modulus ∧
      (doubleWords spec x y curveA).2.toNat < spec.modulus := by
  constructor
  · exact subValue_canonical spec _ _ (addValue_canonical spec _ _)
  · exact subValue_canonical spec _ _ yCanonical

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
