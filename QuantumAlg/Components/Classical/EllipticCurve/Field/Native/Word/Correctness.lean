/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub.Word
import Mathlib.Data.ZMod.Basic

/-!
# Canonical field interpretation of actual finite-word arithmetic

The words computed by native addition and multiplication store a reduced
natural expression. Its canonical range makes the final narrowing exact,
including an admitted modulus equal to the word capacity. The original
subtraction word has the corresponding field interpretation when its right
operand is canonical. Raw inputs outside that subtraction domain retain
their actual wrapping behavior and receive no unsupported field equation.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

open ClassicalAlgorithms.Modular

variable {width : Nat}

/-- Narrowing an actual reduced natural expression preserves its complete residue value. -/
theorem fieldWordOfNat_mod_toNat (spec : ModulusSpec width) (value : Nat) :
    (CShape.wordOfNat width (value % spec.modulus)).toNat = value % spec.modulus := by
  change (value % spec.modulus) % 2 ^ width = value % spec.modulus
  exact Nat.mod_eq_of_lt ((Nat.mod_lt value (modulusSpec_modulus_pos spec)).trans_le
    spec.le_capacity)

/-- Every such actual reduced word is canonical below the original modulus. -/
theorem fieldWordOfNat_mod_canonical (spec : ModulusSpec width) (value : Nat) :
    (CShape.wordOfNat width (value % spec.modulus)).toNat < spec.modulus := by
  rw [fieldWordOfNat_mod_toNat]
  exact Nat.mod_lt value (modulusSpec_modulus_pos spec)

/-- The actual reduced word represents the same element of the original residue ring. -/
theorem fieldWordOfNat_mod_cast (spec : ModulusSpec width) (value : Nat) :
    ((CShape.wordOfNat width (value % spec.modulus)).toNat : ZMod spec.modulus) = value := by
  rw [fieldWordOfNat_mod_toNat, ZMod.natCast_mod]

/-- Native addition's reduced result is canonical for all raw input words. -/
theorem fieldAddWord_canonical (spec : ModulusSpec width) (left right : CShape.Word width) :
    (CShape.wordOfNat width ((left.toNat + right.toNat) % spec.modulus)).toNat < spec.modulus :=
  fieldWordOfNat_mod_canonical spec (left.toNat + right.toNat)

/-- Native addition's actual result has the original residue-ring sum. -/
theorem fieldAddWord_cast (spec : ModulusSpec width) (left right : CShape.Word width) :
    ((CShape.wordOfNat width ((left.toNat + right.toNat) % spec.modulus)).toNat :
      ZMod spec.modulus) = (left.toNat : ZMod spec.modulus) + right.toNat := by
  rw [fieldWordOfNat_mod_cast, Nat.cast_add]

/-- Native multiplication's reduced result is canonical for all raw input words. -/
theorem fieldMulWord_canonical (spec : ModulusSpec width) (left right : CShape.Word width) :
    (CShape.wordOfNat width ((left.toNat * right.toNat) % spec.modulus)).toNat < spec.modulus :=
  fieldWordOfNat_mod_canonical spec (left.toNat * right.toNat)

/-- Native multiplication's actual result has the original residue-ring product. -/
theorem fieldMulWord_cast (spec : ModulusSpec width) (left right : CShape.Word width) :
    ((CShape.wordOfNat width ((left.toNat * right.toNat) % spec.modulus)).toNat :
      ZMod spec.modulus) = (left.toNat : ZMod spec.modulus) * right.toNat := by
  rw [fieldWordOfNat_mod_cast, Nat.cast_mul]

/-- The original canonical-right subtraction domain gives a canonical actual result. -/
theorem subtractionWord_canonical (spec : ModulusSpec width) (left right : CShape.Word width)
    (rightCanonical : right.toNat < spec.modulus) :
    (subtractionWord spec left right).toNat < spec.modulus := by
  rw [subtractionWord_toNat spec left right rightCanonical]
  exact Nat.mod_lt _ (modulusSpec_modulus_pos spec)

/-- The real widened subtraction and reduction give the original residue-ring difference. -/
theorem subtractionWord_cast (spec : ModulusSpec width) (left right : CShape.Word width)
    (rightCanonical : right.toNat < spec.modulus) :
    ((subtractionWord spec left right).toNat : ZMod spec.modulus) =
      (left.toNat : ZMod spec.modulus) - right.toNat := by
  have noBorrow : right.toNat ≤ left.toNat + spec.modulus := by omega
  rw [subtractionWord_toNat spec left right rightCanonical, ZMod.natCast_mod,
    Nat.cast_sub noBorrow, Nat.cast_add, ZMod.natCast_self, add_zero]

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native
