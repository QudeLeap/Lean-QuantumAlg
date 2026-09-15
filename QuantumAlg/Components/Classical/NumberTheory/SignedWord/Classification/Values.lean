/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord

/-!
# Two's-complement sign and magnitude

The most-significant bit is the sign predicate for every positive width.
The unique zero-width word is nonnegative and has magnitude zero.
Conditional complement and increment give the exact unsigned magnitude.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord

/-- Whether an arbitrary raw word has its two's-complement sign bit set. -/
def rawIsNegative {width : Nat} (raw : CShape.Word width) : Bool :=
  decide (2 ^ (width - 1) ≤ raw.toNat)

/-- Unsigned magnitude obtained by conditional two's-complement negation. -/
def rawMagnitude {width : Nat} (raw : CShape.Word width) : Nat :=
  if rawIsNegative raw then
    CShape.wordModulus width - raw.toNat
  else
    raw.toNat

/-- Fixed-width complement followed by increment realizes unsigned
two's-complement magnitude for every nonzero input. -/
theorem complementIncrement_toNat {width : Nat} (input : CShape.Word width)
    (inputPositive : 0 < input.toNat) :
    (Resource.WordUnaryOpcode.eval .increment width
      (Resource.WordUnaryOpcode.eval .complement width input)).toNat =
        CShape.wordModulus width - input.toNat := by
  have inputRange : input.toNat < CShape.wordModulus width :=
    input.toNat_lt
  have complementRange :
      CShape.wordModulus width - 1 - input.toNat <
        CShape.wordModulus width := by
    omega
  have resultRange :
      CShape.wordModulus width - input.toNat <
        CShape.wordModulus width := by
    omega
  simp only [Resource.WordUnaryOpcode.eval, CShape.wordComplement,
    CShape.wordOfNat_val]
  rw [Nat.mod_eq_of_lt complementRange]
  have numeratorEq :
      CShape.wordModulus width - 1 - input.toNat + 1 =
        CShape.wordModulus width - input.toNat := by
    omega
  rw [numeratorEq, Nat.mod_eq_of_lt resultRange]

/-- A raw word classified as negative is necessarily nonzero. -/
theorem rawIsNegative_true_toNat_pos {width : Nat}
    (raw : CShape.Word width) (negative : rawIsNegative raw = true) :
    0 < raw.toNat := by
  have thresholdPositive : 0 < 2 ^ (width - 1) := Nat.two_pow_pos _
  have thresholdLe : 2 ^ (width - 1) ≤ raw.toNat := by
    unfold rawIsNegative at negative
    exact of_decide_eq_true negative
  omega

/-- The statically addressed most-significant bit is exactly the signed threshold predicate. -/
theorem rawIsNegative_eq_signBit {width : Nat} (raw : CShape.Word (width + 1)) :
    (raw.wordBitGet ⟨0, Nat.succ_pos width⟩).toBool = rawIsNegative raw := by
  cases raw with
  | unsignedWord value =>
      change value.val.testBit width = decide (2 ^ width ≤ value.val)
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have positive : 0 < 2 ^ width := Nat.two_pow_pos width
      have bounded : value.val / 2 ^ width < 2 := by
        apply (Nat.div_lt_iff_lt_mul positive).2
        simpa only [pow_succ, Nat.mul_comm] using value.isLt
      by_cases high : 2 ^ width ≤ value.val
      · have lower : 1 ≤ value.val / 2 ^ width := by
          apply (Nat.le_div_iff_mul_le positive).2
          simpa using high
        have quotient : value.val / 2 ^ width = 1 := by omega
        simp [quotient, high]
      · have quotient : value.val / 2 ^ width = 0 := Nat.div_eq_of_lt (by omega)
        simp [quotient, high]

/-- The unique zero-width word has no sign bit and is nonnegative. -/
theorem rawIsNegative_zero (raw : CShape.Word 0) : rawIsNegative raw = false := by
  have zero : raw.toNat = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ raw.toNat_lt)
  simp [rawIsNegative, zero]

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord
