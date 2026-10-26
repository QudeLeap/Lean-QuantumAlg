/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.ScanMetadata

/-!
# Complete finite metadata geometry without overflow aliases

A temporary word with two bits beyond an original metadata field retains
all three summands and the separator. Its modular negative values cannot
alias a valid positive physical window length. These statements cover all
finite metadata words, independently of any reachable EEA trajectory.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.ScanGeometry

/-- The complete temporary arithmetic carrier fits in the already declared pool. -/
abbrev fullWidth (width : Nat) : Nat := width.size + 2

/-- The physical work-word length fits strictly in the complete temporary carrier. -/
lemma target_lt (width : Nat) : width + 3 < 2 ^ fullWidth width := by
  have range := Nat.lt_size_self width
  have positive := Nat.two_pow_pos width.size
  simp only [fullWidth, Nat.pow_succ]
  omega

/-- No complete three-field remainder sum, including the separator, loses a high carry. -/
lemma remainder_sum_lt {width : Nat}
    (coefficient quotient shift : BitVec width.size) :
    coefficient.toNat + quotient.toNat + 1 + shift.toNat < 2 ^ fullWidth width := by
  have left := coefficient.isLt
  have middle := quotient.isLt
  have right := shift.isLt
  have positive := Nat.two_pow_pos width.size
  simp only [fullWidth, Nat.pow_succ]
  omega

/-- Unsigned residue of the exact mathematical difference in one complete temporary carrier. -/
def residue (capacity length total : Nat) : Nat :=
  (capacity + length - total) % capacity

/-- A wrapped negative difference never becomes an admissible positive window length. -/
lemma residue_positive_iff (capacity length total : Nat)
    (bounded : length < capacity) (full : total < capacity) :
    (0 < residue capacity length total ∧ residue capacity length total ≤ length) ↔
      total < length := by
  by_cases fits : total ≤ length
  · have difference : capacity + length - total = capacity + (length - total) := by omega
    have small : length - total < capacity := by omega
    have exactValue : residue capacity length total = length - total := by
      rw [residue, difference, Nat.add_mod, Nat.mod_self, Nat.zero_add,
        Nat.mod_eq_of_lt small]
      exact Nat.mod_eq_of_lt small
    rw [exactValue]
    omega
  · have wrapped : capacity + length - total < capacity := by omega
    have tooLarge : length < capacity + length - total := by omega
    rw [residue, Nat.mod_eq_of_lt wrapped]
    omega

/-- Every full finite remainder key is checked against its untruncated natural physical boundary. -/
lemma remainder_positive_iff {width : Nat}
    (coefficient quotient shift : BitVec width.size) :
    (0 < residue (2 ^ fullWidth width) (width + 3)
        (coefficient.toNat + quotient.toNat + 1 + shift.toNat) ∧
      residue (2 ^ fullWidth width) (width + 3)
        (coefficient.toNat + quotient.toNat + 1 + shift.toNat) ≤ width + 3) ↔
      coefficient.toNat + quotient.toNat + 1 + shift.toNat < width + 3 :=
  residue_positive_iff _ _ _ (target_lt width) (remainder_sum_lt coefficient quotient shift)

end QuantumAlg.NumberTheory.SharedEEA.ScanGeometry
