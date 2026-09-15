/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.Reduce.Native.Semantics

/-!
# Exact finite-word arithmetic of the original field subtraction

These expressions use the same closed widening, add-with-carry,
subtract-with-borrow and reduction operations as the native program. The
original canonical-right condition makes subtraction nonnegative; malformed
raw inputs retain the actual wrapping word semantics rather than acquiring
an unsupported field-arithmetic interpretation.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

open ClassicalAlgorithms.Modular Modular.Reduce.Native

variable {width : Nat}

/-- The real widened modulus value loaded by both original constant-word programs. -/
def subtractionModulusWord (spec : ModulusSpec width) : CShape.Word (width + 1) :=
  CShape.wordOfNat (width + 1) spec.modulus

/-- The actual low-word component of the original widened left-plus-modulus instruction. -/
def subtractionAugmentedWord (spec : ModulusSpec width) (left : CShape.Word width) :
    CShape.Word (width + 1) :=
  (CShape.addCarry (width + 1)
    (.product (CShape.wordResize (width + 1) left) (subtractionModulusWord spec))).first

/-- Actual low-word subtraction preserves wrapping behavior on every raw right input. -/
def subtractionDifferenceWord (spec : ModulusSpec width) (left right : CShape.Word width) :
    CShape.Word (width + 1) :=
  (CShape.subBorrow (width + 1) (.product (subtractionAugmentedWord spec left)
    (CShape.wordResize (width + 1) right))).first

/-- The exact finite-word result of the actual raw subtraction followed by original reduction. -/
def subtractionWord (spec : ModulusSpec width) (left right : CShape.Word width) :
    CShape.Word width :=
  reductionValue (subtractionDifferenceWord spec left right) (subtractionModulusWord spec)

/-- The extended shape stores every original admitted modulus, including the full capacity. -/
theorem subtractionModulusWord_toNat (spec : ModulusSpec width) :
    (subtractionModulusWord spec).toNat = spec.modulus :=
  Nat.mod_eq_of_lt (modulusSpec_modulus_lt_extended spec)

private theorem subtraction_widened_toNat (value : CShape.Word width) :
    (CShape.wordResize (width + 1) value).toNat = value.toNat := by
  change value.toNat % 2 ^ (width + 1) = _
  apply Nat.mod_eq_of_lt
  have bound := value.toNat_lt
  rw [pow_succ]
  omega

/-- The original first arithmetic sum is exact even for arbitrary raw left inputs. -/
theorem subtractionAugmentedWord_toNat (spec : ModulusSpec width) (left : CShape.Word width) :
    (subtractionAugmentedWord spec left).toNat = left.toNat + spec.modulus := by
  change ((CShape.wordResize (width + 1) left).toNat +
    (subtractionModulusWord spec).toNat) % 2 ^ (width + 1) = _
  rw [subtraction_widened_toNat, subtractionModulusWord_toNat]
  apply Nat.mod_eq_of_lt
  have leftBound := left.toNat_lt
  have modulusBound : spec.modulus ≤ 2 ^ width := spec.le_capacity
  rw [pow_succ]
  omega

private theorem subtraction_word_mod_sub (initial subtract capacity : Nat)
    (noBorrow : subtract ≤ initial) (fits : initial < capacity) :
    (initial + capacity - subtract) % capacity = initial - subtract := by
  have regroup : initial + capacity - subtract = (initial - subtract) + capacity := by omega
  rw [regroup, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) fits)

/-- The original canonical-right domain makes the actual low subtraction word nonnegative. -/
theorem subtractionDifferenceWord_toNat (spec : ModulusSpec width)
    (left right : CShape.Word width)
    (rightCanonical : right.toNat < spec.modulus) :
    (subtractionDifferenceWord spec left right).toNat =
      left.toNat + spec.modulus - right.toNat := by
  change ((subtractionAugmentedWord spec left).toNat + 2 ^ (width + 1) -
    (CShape.wordResize (width + 1) right).toNat) % 2 ^ (width + 1) = _
  rw [subtractionAugmentedWord_toNat, subtraction_widened_toNat]
  apply subtraction_word_mod_sub
  · omega
  · have leftBound := left.toNat_lt
    have modulusBound : spec.modulus ≤ 2 ^ width := spec.le_capacity
    rw [pow_succ]
    omega

/-- The original canonical operand domain gives exact native field subtraction. -/
theorem subtractionWord_toNat (spec : ModulusSpec width) (left right : CShape.Word width)
    (rightCanonical : right.toNat < spec.modulus) :
    (subtractionWord spec left right).toNat =
      (left.toNat + spec.modulus - right.toNat) % spec.modulus := by
  have modulusValue := subtractionModulusWord_toNat spec
  rw [subtractionWord, reductionValue_toNat _ _
    (modulusValue ▸ modulusSpec_modulus_pos spec) (modulusValue ▸ spec.le_capacity),
    modulusValue, subtractionDifferenceWord_toNat spec left right rightCanonical]

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native
