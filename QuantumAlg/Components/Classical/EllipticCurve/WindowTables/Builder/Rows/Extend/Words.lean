/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Arithmetic

/-!
# Original finite-word coordinate-extension expressions

The literal batch-inverse word is an input read from C. These expressions
follow the original paid secant slots; no inverse or coordinate value is
supplied to the actual program constructor.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open ClassicalAlgorithms.Modular Modular.NativePower Field.Native.Shared

noncomputable section

variable {width : Nat}

/-- Exact finite-word expressions of the original coordinate extension. -/
def extendWords (spec : ModulusSpec width) (x y baseX baseY inverse : CShape.Word width) :
    CShape.Word width × CShape.Word width :=
  let modulus : CShape.Word (width + 1) := .unsignedWord spec.extendedWord
  let slope := multiplyValue (subValue baseY y modulus) inverse modulus
  let nextX := subValue (subValue (multiplyValue slope slope modulus) x modulus) baseX modulus
  let nextY := subValue (multiplyValue slope (subValue x nextX modulus) modulus) y modulus
  (nextX, nextY)

/-- The real result coordinates are canonical on the original canonical input-coordinate domain. -/
lemma extendWords_canonical (spec : ModulusSpec width)
    (x y baseX baseY inverse : CShape.Word width)
    (yCanonical : y.toNat < spec.modulus) (baseXCanonical : baseX.toNat < spec.modulus) :
    (extendWords spec x y baseX baseY inverse).1.toNat < spec.modulus ∧
      (extendWords spec x y baseX baseY inverse).2.toNat < spec.modulus := by
  exact ⟨subValue_canonical spec _ _ baseXCanonical, subValue_canonical spec _ _ yCanonical⟩

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
