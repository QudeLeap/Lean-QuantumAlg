/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Signed.Division

/-!
# Exact remainder arithmetic above an unchanged low binary suffix

The source's actual remainder window stops before the last shift bits of
Work1, while the aligned Work2 window contains the divisor
[LYL+26, sec_EEA/sub_regshare.tex:263-278;
LYL+26, sec_EEA/sub_opt.tex:43-48]. Thus the native subtraction compares
the high part of the remainder with the divisor. Reattaching the unchanged
low suffix gives comparison and subtraction of the full shifted threshold.

These identities hold for every natural remainder, divisor, and shift.
They require no divisibility or zero-low-suffix premise. Equality uses the
weak subtraction branch, matching the strict borrow bit of signed words.
This is the mathematical scale bridge; actual physical extraction and
native Sign/quotient exchange are proved at their own implementation owners.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.DivisionScale

/-- The complete remainder is exactly its high window followed by its arbitrary low suffix. -/
theorem reassemble (remainder shift : Nat) :
    remainder / 2 ^ shift * 2 ^ shift + remainder % 2 ^ shift = remainder :=
  Nat.div_add_mod' remainder (2 ^ shift)

/-- The actual high-window comparison is the full comparison with the shifted threshold. -/
theorem comparison (remainder divisor shift : Nat) :
    divisor ≤ remainder / 2 ^ shift ↔ divisor * 2 ^ shift ≤ remainder := by
  constructor
  · intro selected
    exact (Nat.mul_le_mul_right (2 ^ shift) selected).trans
      (Nat.div_mul_le_self remainder (2 ^ shift))
  · intro selected
    by_contra rejected
    have smaller := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos shift)).mp (Nat.lt_of_not_ge rejected)
    omega

/-- Strict high-window underflow is exactly underflow of the complete shifted subtraction. -/
theorem underflow (remainder divisor shift : Nat) :
    remainder / 2 ^ shift < divisor ↔ remainder < divisor * 2 ^ shift :=
  Nat.div_lt_iff_lt_mul (Nat.two_pow_pos shift)

/-- The unchanged low suffix reassembles the actual conditional high subtraction exactly. -/
theorem corrected_reassemble (remainder divisor shift : Nat) :
    (if divisor ≤ remainder / 2 ^ shift
      then remainder / 2 ^ shift - divisor else remainder / 2 ^ shift) * 2 ^ shift +
        remainder % 2 ^ shift =
      if divisor * 2 ^ shift ≤ remainder then remainder - divisor * 2 ^ shift else remainder := by
  have complete := reassemble remainder shift
  by_cases selected : divisor ≤ remainder / 2 ^ shift
  · have selectedFull := (comparison remainder divisor shift).mp selected
    have scaled := Nat.mul_le_mul_right (2 ^ shift) selected
    rw [if_pos selected, if_pos selectedFull, Nat.sub_mul]
    omega
  · have rejectedFull : ¬divisor * 2 ^ shift ≤ remainder :=
      fun selectedFull => selected ((comparison remainder divisor shift).mpr selectedFull)
    rw [if_neg selected, if_neg rejectedFull]
    exact complete

/-- An actual corrected finite high window plus its original low suffix gives full subtraction. -/
theorem word_corrected_reassemble {width : Nat} (value divisor : BitVec width)
    (remainder shift : Nat) (high : value.toNat = remainder / 2 ^ shift) :
    (SignedDivision.corrected value divisor).toNat * 2 ^ shift + remainder % 2 ^ shift =
      if divisor.toNat * 2 ^ shift ≤ remainder
      then remainder - divisor.toNat * 2 ^ shift else remainder := by
  rw [SignedDivision.corrected_toNat, high]
  exact corrected_reassemble remainder divisor.toNat shift

/-- A nonzero suffix exercises equality and rejected subtraction without extra assumptions. -/
theorem nonzero_suffix_equality :
    5 % 2 = 1 ∧
      (if 2 ≤ 5 / 2 then 5 / 2 - 2 else 5 / 2) * 2 + 5 % 2 = 1 ∧
      (if 3 ≤ 5 / 2 then 5 / 2 - 3 else 5 / 2) * 2 + 5 % 2 = 5 := by
  decide

end QuantumAlg.NumberTheory.SharedEEA.DivisionScale
