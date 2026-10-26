/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Arithmetic

/-!
# Finite-word values of the original final five-column conversion

These expressions are the original row's arithmetic results in their actual
write order. They interpret only the paid row slots; they are not executable
native operations and do not replace table reads or coefficient programs.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open ClassicalAlgorithms.Modular Modular.NativePower Field.Native.Shared

noncomputable section

variable {width : Nat}

/-- The literal finite-word results of the final row's five actual destination writes. -/
def finishWords (spec : ModulusSpec width)
    (x y curveA inverse zero one : CShape.Word width) : Fin 5 → CShape.Word width :=
  let modulus : CShape.Word (width + 1) := .unsignedWord spec.extendedWord
  let square := multiplyValue x x modulus
  let numerator := addValue (addValue (addValue square square modulus) square modulus)
    curveA modulus
  ![subValue zero x modulus, subValue zero y modulus,
    addValue (addValue x x modulus) x modulus,
    multiplyValue numerator inverse modulus, addValue x one modulus]

/-- Each literal output represents its original field expression, including the supplied inverse. -/
lemma finishWords_cast (spec : ModulusSpec width)
    (x y curveA inverse zero one : CShape.Word width)
    (xCanonical : x.toNat < spec.modulus) (yCanonical : y.toNat < spec.modulus)
    (zeroValue : zero.toNat = 0) (oneValue : one.toNat = 1) (index : Fin 5) :
    ((finishWords spec x y curveA inverse zero one index).toNat : ZMod spec.modulus) =
      ![-(x.toNat : ZMod spec.modulus), -(y.toNat : ZMod spec.modulus),
        3 * (x.toNat : ZMod spec.modulus),
        (3 * (x.toNat : ZMod spec.modulus) ^ 2 + curveA.toNat) * inverse.toNat,
        (x.toNat : ZMod spec.modulus) + 1] index := by
  fin_cases index
  · change ((subValue zero x _).toNat : ZMod spec.modulus) = -(x.toNat : ZMod spec.modulus)
    rw [subValue_cast spec _ _ xCanonical, zeroValue, Nat.cast_zero, zero_sub]
  · change ((subValue zero y _).toNat : ZMod spec.modulus) = -(y.toNat : ZMod spec.modulus)
    rw [subValue_cast spec _ _ yCanonical, zeroValue, Nat.cast_zero, zero_sub]
  · change ((addValue (addValue x x _) x _).toNat : ZMod spec.modulus) =
      3 * (x.toNat : ZMod spec.modulus)
    rw [addValue_cast, addValue_cast]
    ring
  · change ((multiplyValue (addValue (addValue
      (addValue (multiplyValue x x _) (multiplyValue x x _) _) (multiplyValue x x _) _)
      curveA _) inverse _).toNat : ZMod spec.modulus) =
      (3 * (x.toNat : ZMod spec.modulus) ^ 2 + curveA.toNat) * inverse.toNat
    simp only [multiplyValue_cast, addValue_cast]
    ring
  · change ((addValue x one _).toNat : ZMod spec.modulus) =
      (x.toNat : ZMod spec.modulus) + 1
    rw [addValue_cast, oneValue, Nat.cast_one]

/-- All five real finite-word output expressions are canonical on the original coordinate domain. -/
lemma finishWords_canonical (spec : ModulusSpec width)
    (x y curveA inverse zero one : CShape.Word width)
    (xCanonical : x.toNat < spec.modulus) (yCanonical : y.toNat < spec.modulus)
    (index : Fin 5) :
    (finishWords spec x y curveA inverse zero one index).toNat < spec.modulus := by
  fin_cases index
  · exact subValue_canonical spec _ _ xCanonical
  · exact subValue_canonical spec _ _ yCanonical
  · exact addValue_canonical spec _ _
  · exact multiplyValue_canonical spec _ _
  · exact addValue_canonical spec _ _

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
