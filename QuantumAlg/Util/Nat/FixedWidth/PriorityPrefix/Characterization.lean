/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.PriorityPrefix

/-! # The numeric first-one position is exactly the first marked original source bit -/

namespace QuantumAlg.NatFixedWidth.PriorityPrefix

/-- Every earlier most-significant-first position is zero, including the whole zero-source word. -/
lemma before_firstOne {width : Nat} (word : BitVec width) (index : Nat)
    (earlier : index < firstOne word) : word.getMsbD index = false := by
  have sourceSize : word.toNat.size ≤ width := Nat.size_le.mpr word.isLt
  have fits : index < width := earlier.trans_le (firstOne_le word)
  have exponent : word.toNat.size ≤ width - 1 - index := by
    unfold firstOne at earlier
    omega
  have below := (Nat.lt_size_self word.toNat).trans_le
    (Nat.pow_le_pow_right Nat.zero_lt_two exponent)
  have zero := Nat.testBit_lt_two_pow below
  simpa only [BitVec.getMsbD_eq_getLsbD, fits, decide_true, Bool.true_and,
    BitVec.getLsbD] using zero

/-- A nonsentinel first-one position contains its actual source one bit. -/
lemma at_firstOne {width : Nat} (word : BitVec width) (present : firstOne word < width) :
    word.getMsbD (firstOne word) = true := by
  have sourceSize : word.toNat.size ≤ width := Nat.size_le.mpr word.isLt
  have positive : 0 < word.toNat.size := by
    unfold firstOne at present
    omega
  have position : width - 1 - firstOne word = word.toNat.size - 1 := by
    unfold firstOne
    omega
  have lower : 2 ^ (word.toNat.size - 1) ≤ word.toNat :=
    Nat.lt_size.mp (by omega)
  have upper : word.toNat < 2 ^ (word.toNat.size - 1 + 1) := by
    have same : word.toNat.size - 1 + 1 = word.toNat.size := by omega
    rw [same]
    exact Nat.lt_size_self word.toNat
  have selected := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt lower upper
  simpa only [BitVec.getMsbD_eq_getLsbD, present, decide_true, Bool.true_and,
    position, BitVec.getLsbD] using selected

/-- Every first-marked result, with width as zero sentinel, has this numeric value. -/
lemma firstOne_unique {width : Nat} (word : BitVec width) (index : Nat) (fits : index ≤ width)
    (earlier : ∀ before, before < index → word.getMsbD before = false)
    (selected : index < width → word.getMsbD index = true) : index = firstOne word := by
  by_cases before : index < firstOne word
  · have zero := before_firstOne word index before
    have one := selected (before.trans_le (firstOne_le word))
    rw [zero] at one
    cases one
  · by_cases after : firstOne word < index
    · have zero := earlier (firstOne word) after
      have one := at_firstOne word (after.trans_le fits)
      rw [zero] at one
      cases one
    · omega

end QuantumAlg.NatFixedWidth.PriorityPrefix
