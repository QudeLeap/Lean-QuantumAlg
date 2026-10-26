/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega

/-! # Complete unsigned radix windows and original binary bit positions -/

namespace QuantumAlg.Nat.FixedWidth.Radix

/-- One original unsigned digit, starting from the least significant window. -/
def digit (radix value index : Nat) : Nat := value / radix ^ index % radix

/-- Prefix weight of the original low-to-high unsigned digit schedule. -/
def prefixValue (radix value : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => prefixValue radix value count + radix ^ count * digit radix value count

lemma prefix_eq_mod (radix value count : Nat) :
    prefixValue radix value count = value % radix ^ count := by
  induction count with
  | zero => exact (Nat.mod_one value).symm
  | succ count ih =>
      rw [prefixValue, ih, Nat.mod_pow_succ]
      rfl

lemma prefix_full {radix value count : Nat} (bounded : value < radix ^ count) :
    prefixValue radix value count = value :=
  (prefix_eq_mod radix value count).trans (Nat.mod_eq_of_lt bounded)

open scoped BigOperators

/-- The literal finite window weights have the same low-to-high prefix value. -/
lemma sum_digits (radix value count : Nat) :
    (∑ index : Fin count, radix ^ index.val * digit radix value index.val) =
      prefixValue radix value count := by
  induction count with
  | zero => simp only [Finset.univ_eq_empty, Finset.sum_empty, prefixValue]
  | succ count ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, prefixValue, ih]

/-- A binary radix digit reads precisely the corresponding original little-endian source bits. -/
lemma binary_digit_bit (chunk value window : Nat) (bit : Fin chunk) :
    (digit (2 ^ chunk) value window).testBit bit.val =
      value.testBit (chunk * window + bit.val) := by
  rw [digit, ← Nat.pow_mul, Nat.testBit_mod_two_pow, decide_eq_true bit.isLt, Bool.true_and,
    Nat.testBit_div_two_pow, Nat.add_comm]

/-- The untruncated tail after a full-width prefix retains its original smaller bound. -/
lemma binary_tail_lt {value prefixWidth tailWidth : Nat}
    (bounded : value < 2 ^ (prefixWidth + tailWidth)) :
    value / 2 ^ prefixWidth < 2 ^ tailWidth := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos prefixWidth)]
  simpa only [Nat.pow_add, Nat.mul_comm] using bounded

/-- An original final digit respects its smaller tail bound before closed-width specialization. -/
lemma binary_tail_digit_lt {value chunk window tailWidth : Nat}
    (bounded : value < 2 ^ (chunk * window + tailWidth)) :
    digit (2 ^ chunk) value window < 2 ^ tailWidth := by
  have quotient := binary_tail_lt bounded
  rw [digit, ← Nat.pow_mul]
  exact (Nat.mod_le _ _).trans_lt quotient

/-- An explicitly certified original width retains its exact exponent without evaluating powers. -/
lemma binary_tail_digit_lt_of_width {value width chunk window tailWidth : Nat}
    (widthEq : width = chunk * window + tailWidth) (bounded : value < 2 ^ width) :
    digit (2 ^ chunk) value window < 2 ^ tailWidth := by
  subst width
  exact binary_tail_digit_lt bounded

/-- A complete binary exponent fits all original unsigned windows. -/
lemma binary_capacity {width chunk windows : Nat} (bounded : width ≤ chunk * windows) :
    2 ^ width ≤ (2 ^ chunk) ^ windows := by
  rw [← Nat.pow_mul]
  exact Nat.pow_le_pow_right (by decide) bounded

end QuantumAlg.Nat.FixedWidth.Radix
