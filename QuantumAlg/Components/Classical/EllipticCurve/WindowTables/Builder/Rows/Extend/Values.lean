/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Extend.Words

/-!
# Field interpretation of the original coordinate-extension words

The supplied equality describes the actual preceding batch's C word. The
same finite-word expressions then give the conventional secant formulas.
Canonical coordinate premises justify each original modular subtraction.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open ClassicalAlgorithms.Modular Modular.NativePower Field.Native.Shared

noncomputable section

variable {width : Nat}

/-- The literal coordinate words give the original secant formulas on the actual inverse domain. -/
lemma extendWords_cast (spec : ModulusSpec width)
    (x y baseX baseY inverse : CShape.Word width)
    (xCanonical : x.toNat < spec.modulus) (yCanonical : y.toNat < spec.modulus)
    (baseXCanonical : baseX.toNat < spec.modulus)
    (inverseValue : (inverse.toNat : ZMod spec.modulus) =
      ((baseX.toNat : ZMod spec.modulus) - x.toNat)⁻¹) :
    let slope : ZMod spec.modulus :=
      (baseY.toNat - (y.toNat : ZMod spec.modulus)) *
        ((baseX.toNat : ZMod spec.modulus) - x.toNat)⁻¹
    let nextX := slope ^ 2 - x.toNat - baseX.toNat
    ((extendWords spec x y baseX baseY inverse).1.toNat : ZMod spec.modulus) = nextX ∧
      ((extendWords spec x y baseX baseY inverse).2.toNat : ZMod spec.modulus) =
        slope * (x.toNat - nextX) - y.toNat := by
  let modulus : CShape.Word (width + 1) := .unsignedWord spec.extendedWord
  let slopeWord := multiplyValue (subValue baseY y modulus) inverse modulus
  let nextXWord := subValue (subValue (multiplyValue slopeWord slopeWord modulus) x modulus)
    baseX modulus
  let nextYWord := subValue
    (multiplyValue slopeWord (subValue x nextXWord modulus) modulus) y modulus
  let slopeField : ZMod spec.modulus :=
    (baseY.toNat - (y.toNat : ZMod spec.modulus)) *
      ((baseX.toNat : ZMod spec.modulus) - x.toNat)⁻¹
  have slopeCast : (slopeWord.toNat : ZMod spec.modulus) = slopeField := by
    change ((multiplyValue (subValue baseY y (.unsignedWord spec.extendedWord)) inverse
      (.unsignedWord spec.extendedWord)).toNat : ZMod spec.modulus) = _
    rw [multiplyValue_cast, subValue_cast spec _ _ yCanonical, inverseValue]
  have nextXCanonical : nextXWord.toNat < spec.modulus :=
    subValue_canonical spec _ _ baseXCanonical
  have nextXCast : (nextXWord.toNat : ZMod spec.modulus) =
      slopeField ^ 2 - x.toNat - baseX.toNat := by
    change ((subValue (subValue (multiplyValue slopeWord slopeWord
      (.unsignedWord spec.extendedWord)) x (.unsignedWord spec.extendedWord))
      baseX (.unsignedWord spec.extendedWord)).toNat : ZMod spec.modulus) = _
    rw [subValue_cast spec _ _ baseXCanonical, subValue_cast spec _ _ xCanonical,
      multiplyValue_cast, slopeCast]
    ring
  have nextYCast : (nextYWord.toNat : ZMod spec.modulus) =
      slopeField * (x.toNat - (slopeField ^ 2 - x.toNat - baseX.toNat)) - y.toNat := by
    change ((subValue (multiplyValue slopeWord
      (subValue x nextXWord (.unsignedWord spec.extendedWord))
      (.unsignedWord spec.extendedWord)) y (.unsignedWord spec.extendedWord)).toNat :
      ZMod spec.modulus) = _
    rw [subValue_cast spec _ _ yCanonical, multiplyValue_cast,
      subValue_cast spec _ _ nextXCanonical, slopeCast, nextXCast]
  exact ⟨nextXCast, nextYCast⟩

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
