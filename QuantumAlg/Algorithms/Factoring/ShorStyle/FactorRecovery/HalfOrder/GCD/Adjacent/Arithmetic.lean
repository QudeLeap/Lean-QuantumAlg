/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.ClassicalOp
import Mathlib.Data.Nat.Bitwise

/-!
# Exact finite arithmetic of the adjacent half-power words

The extra bit preserves every original word and its successor. A wrapping
decrement has that bit set precisely for original zero, so the real selected
clear in the predecessor circuit implements natural subtraction exactly.
The statements also cover the zero-width original word.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeAdjacentWord

variable {width : Nat}

/-- The actual widening keeps the entire original unsigned value. -/
theorem resize_toNat (value : CShape.Word width) :
    (CShape.wordResize (width + 1) value).toNat = value.toNat := by
  have bounded := value.toNat_lt
  change value.toNat % 2 ^ (width + 1) = value.toNat
  apply Nat.mod_eq_of_lt
  have doubled : 2 ^ (width + 1) = 2 ^ width * 2 := Nat.pow_succ 2 width
  have positive := Nat.two_pow_pos width
  omega

/-- The new bit makes the genuine increment exact even at the old maximal word. -/
theorem increment_toNat (value : CShape.Word width) :
    (Resource.WordUnaryOpcode.eval .increment (width + 1)
      (CShape.wordResize (width + 1) value)).toNat = value.toNat + 1 := by
  change ((CShape.wordResize (width + 1) value).toNat + 1) % 2 ^ (width + 1) = _
  rw [resize_toNat]
  apply Nat.mod_eq_of_lt
  have bounded := value.toNat_lt
  have doubled : 2 ^ (width + 1) = 2 ^ width * 2 := Nat.pow_succ 2 width
  have positive := Nat.two_pow_pos width
  omega

/-- The real decrement wraps only the original zero into the widened all-ones word. -/
theorem decrement_toNat (value : CShape.Word width) :
    (Resource.WordUnaryOpcode.eval .decrement (width + 1)
      (CShape.wordResize (width + 1) value)).toNat =
      if value.toNat = 0 then 2 ^ (width + 1) - 1 else value.toNat - 1 := by
  have bounded := value.toNat_lt
  have doubled : 2 ^ (width + 1) = 2 ^ width * 2 := Nat.pow_succ 2 width
  have positive := Nat.two_pow_pos width
  have oneBounded : 1 < 2 ^ (width + 1) := by omega
  change ((CShape.wordResize (width + 1) value).toNat + 2 ^ (width + 1) -
      1 % 2 ^ (width + 1)) % 2 ^ (width + 1) = _
  rw [resize_toNat, Nat.mod_eq_of_lt oneBounded]
  by_cases zero : value.toNat = 0
  · rw [if_pos zero, zero, Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [if_neg zero,
      show value.toNat + 2 ^ (width + 1) - 1 = value.toNat - 1 + 2 ^ (width + 1) by omega,
      Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

/-- A structural read of the real highest word bit has the declared numerical index. -/
theorem highBit_toBool (value : CShape.Word (width + 1)) :
    (value.wordBitGet 0).toBool = value.toNat.testBit width := by
  cases value
  rfl

/-- The exact stored underflow bit recognizes original zero, without a comparison callback. -/
theorem decrement_highBit (value : CShape.Word width) :
    ((Resource.WordUnaryOpcode.eval .decrement (width + 1)
      (CShape.wordResize (width + 1) value)).wordBitGet 0).toBool =
      decide (value.toNat = 0) := by
  rw [highBit_toBool, decrement_toNat]
  by_cases zero : value.toNat = 0
  · have doubled : 2 ^ (width + 1) = 2 ^ width * 2 := Nat.pow_succ 2 width
    have positive := Nat.two_pow_pos width
    have quotient : (2 ^ (width + 1) - 1) / 2 ^ width = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [if_pos zero, Nat.testBit_eq_decide_div_mod_eq, quotient, zero]
    decide
  · rw [if_neg zero, Nat.testBit_eq_false_of_lt ((Nat.sub_le _ _).trans_lt value.toNat_lt)]
    simp only [zero, decide_false]

/-- Native self-XOR has exactly zero value, regardless of the actual previous word. -/
theorem selfXor_toNat (value : CShape.Word (width + 1)) :
    (Resource.WordBinaryOpcode.eval .bitXor (width + 1) (.product value value)).toNat = 0 := by
  change (value.toNat ^^^ value.toNat) % 2 ^ (width + 1) = 0
  simp only [Nat.xor_self, Nat.zero_mod]

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeAdjacentWord
