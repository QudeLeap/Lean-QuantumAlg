/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Data.BitVec

/-!
# Independent low-bit identities for the two static modular offsets

For an odd modulus, the original offset and its finite-word difference
from that modulus have complementary least significant bits. This closes
the exact native low-row count without changing any emitted instruction
[G25, main.tex:209-239,253-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction

variable {width : Nat}

/-- Finite-word negation retains the least significant bit, including the empty word. -/
lemma negative_low_bit (value : BitVec width) :
    (-value).getLsbD 0 = value.getLsbD 0 := by
  simp [BitVec.getLsbD_neg]

/-- The least significant subtraction bit has no incoming carry. -/
lemma subtraction_low_bit (first second : BitVec width) (positive : 0 < width) :
    (first - second).getLsbD 0 = (first.getLsbD 0 ^^ second.getLsbD 0) := by
  rw [sub_eq_add_neg, BitVec.getLsbD_add positive]
  simp [negative_low_bit]

/-- Odd modulus makes the two actual static offset low-row contributions complementary. -/
lemma modular_offsets_low_sum (modulus constant : BitVec width) (positive : 0 < width)
    (odd : modulus.getLsbD 0 = true) :
    (constant.getLsbD 0).toNat + ((constant - modulus).getLsbD 0).toNat = 1 := by
  rw [subtraction_low_bit constant modulus positive, odd]
  cases constant.getLsbD 0 <;> rfl

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction
