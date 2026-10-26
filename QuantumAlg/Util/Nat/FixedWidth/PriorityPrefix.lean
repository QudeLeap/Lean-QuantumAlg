/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-!
# Exact size of an initial priority window from a complete first-one position

These are pure finite-word identities. Native first-one encoding,
runtime alignment, finite range tests, copying and cleanup are separate
actual program obligations; none of those operations is supplied here.
-/

namespace QuantumAlg.NatFixedWidth.PriorityPrefix

/-- Removing low positions removes exactly that many positions from the natural binary size. -/
lemma size_shiftRight (value displacement : Nat) :
    (value >>> displacement).size = value.size - displacement := by
  have cut (bound : Nat) :
      (value >>> displacement).size ≤ bound ↔ value.size - displacement ≤ bound := by
    rw [Nat.size_le, Nat.shiftRight_eq_div_pow,
      Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ displacement), ← Nat.pow_add, ← Nat.size_le]
    omega
  exact Nat.le_antisymm ((cut _).mpr (Nat.le_refl _)) ((cut _).mp (Nat.le_refl _))

/-- Highest marked position in most-significant-first order, with width as the zero sentinel. -/
def firstOne {width : Nat} (word : BitVec width) : Nat := width - word.toNat.size

/-- Every position, including the all-zero sentinel, stays within the original width. -/
lemma firstOne_le {width : Nat} (word : BitVec width) : firstOne word ≤ width := Nat.sub_le _ _

/-- The all-zero source uses the complete original width as its sentinel. -/
lemma firstOne_zero (width : Nat) : firstOne (0#width) = width := by
  simp only [firstOne, BitVec.toNat_zero, Nat.size_zero, Nat.sub_zero]

/-- The high prefix has the exact clipped size, including zero length and all-zero words. -/
lemma prefix_size {width : Nat} (word : BitVec width) (length : Nat) (fits : length ≤ width) :
    (word.extractLsb' (width - length) length).toNat.size = length - firstOne word := by
  have sourceSize : word.toNat.size ≤ width := Nat.size_le.mpr word.isLt
  have shiftedSize : (word.toNat >>> (width - length)).size ≤ length := by
    rw [size_shiftRight]
    omega
  rw [BitVec.extractLsb'_toNat, Nat.mod_eq_of_lt (Nat.size_le.mp shiftedSize), size_shiftRight]
  unfold firstOne
  omega

end QuantumAlg.NatFixedWidth.PriorityPrefix
