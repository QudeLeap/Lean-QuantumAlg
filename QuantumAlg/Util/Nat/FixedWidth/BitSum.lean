/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.BitVec
import Mathlib.Data.List.FinRange

/-!
# Complete binary displacement as the sum of every original bit weight

This mathematical identity relates a static sequence of controlled
permutation powers to the full finite metadata value. It supplies no
executed arithmetic operation or quantum resource assumption.
-/

namespace QuantumAlg.Nat.FixedWidth.BitSum

/-- Every position contributes its full original power of two, in increasing index order. -/
def weightedPrefix (number : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => weightedPrefix number count + if number.testBit count then 2 ^ count else 0

/-- The complete low-bit prefix is exactly the natural binary residue. -/
lemma prefix_eq_mod (number count : Nat) : weightedPrefix number count = number % 2 ^ count := by
  induction count with
  | zero => exact (Nat.mod_one number).symm
  | succ count ih =>
      rw [weightedPrefix, ih, Nat.mod_pow_succ]
      congr 1
      rw [← Nat.toNat_testBit]
      cases number.testBit count <;> simp

/-- A complete finite word retains all of its natural displacement without truncation. -/
lemma prefix_toNat {count : Nat} (word : BitVec count) :
    weightedPrefix word.toNat count = word.toNat := by
  rw [prefix_eq_mod, Nat.mod_eq_of_lt word.isLt]

/-- The actual static index list includes exactly every bit once. -/
lemma prefix_eq_range_sum (number count : Nat) :
    weightedPrefix number count =
      ((List.range count).map
        (fun index => if number.testBit index then 2 ^ index else 0)).sum := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [weightedPrefix, List.range_succ, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, ih]

end QuantumAlg.Nat.FixedWidth.BitSum
