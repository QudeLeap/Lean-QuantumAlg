/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Geometry

/-!
# Complete temporary-word subtraction for the natural remainder boundary

All three complete metadata words are extended into the full carrier.
The resulting modular word agrees with the untruncated mathematical
difference. Negative differences cannot masquerade as a valid positive
physical window, including inputs outside an EEA trajectory.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.ScanGeometry

/-- The full temporary carrier retains every bit of an original finite metadata word. -/
def extend {width : Nat} (value : BitVec width.size) : BitVec (fullWidth width) :=
  BitVec.ofNat (fullWidth width) value.toNat

/-- Extending an original finite metadata word retains its complete natural value. -/
lemma extend_toNat {width : Nat} (value : BitVec width.size) :
    (extend value).toNat = value.toNat := by
  have original := value.isLt
  have positive := Nat.two_pow_pos width.size
  change value.toNat % 2 ^ (width.size + 2) = value.toNat
  apply Nat.mod_eq_of_lt
  simp only [Nat.pow_succ]
  omega

/-- Exact modular remainder length with all original metadata and the separator retained. -/
def remainderWord {width : Nat} (coefficient quotient shift : BitVec width.size) :
    BitVec (fullWidth width) :=
  BitVec.ofNat (fullWidth width) (width + 3 - 1) -
    extend coefficient - extend quotient - extend shift

/-- Every full finite three-word geometry has its exact untruncated natural residue. -/
lemma remainderWord_toNat {width : Nat} (coefficient quotient shift : BitVec width.size) :
    (remainderWord coefficient quotient shift).toNat =
      residue (2 ^ fullWidth width) (width + 3)
        (coefficient.toNat + quotient.toNat + 1 + shift.toNat) := by
  have all := remainder_sum_lt coefficient quotient shift
  have coefficientBound : coefficient.toNat < 2 ^ fullWidth width := by omega
  have quotientBound : quotient.toNat < 2 ^ fullWidth width := by omega
  have shiftBound : shift.toNat < 2 ^ fullWidth width := by omega
  have pairBound : coefficient.toNat + quotient.toNat < 2 ^ fullWidth width := by omega
  have sumBound : coefficient.toNat + quotient.toNat + shift.toNat <
      2 ^ fullWidth width := by omega
  have constantBound : width + 3 - 1 < 2 ^ fullWidth width := by
    have := target_lt width
    omega
  have sourceSum : (extend coefficient + extend quotient + extend shift).toNat =
      coefficient.toNat + quotient.toNat + shift.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add]
    simp only [extend, BitVec.toNat_ofNat, Nat.mod_eq_of_lt coefficientBound,
      Nat.mod_eq_of_lt quotientBound, Nat.mod_eq_of_lt shiftBound,
      Nat.mod_eq_of_lt pairBound, Nat.mod_eq_of_lt sumBound]
  rw [remainderWord, BitVec.sub_sub, BitVec.sub_sub, ← BitVec.add_assoc, BitVec.toNat_sub',
    sourceSum, BitVec.toNat_ofNat, Nat.mod_eq_of_lt constantBound, residue]
  apply congrArg (fun value : Nat => value % 2 ^ fullWidth width)
  omega

/-- The actual full-word predicate admits precisely the positive natural remainder windows. -/
lemma remainderWord_positive_iff {width : Nat}
    (coefficient quotient shift : BitVec width.size) :
    (0 < (remainderWord coefficient quotient shift).toNat ∧
      (remainderWord coefficient quotient shift).toNat ≤ width + 3) ↔
      coefficient.toNat + quotient.toNat + 1 + shift.toNat < width + 3 := by
  rw [remainderWord_toNat]
  exact remainder_positive_iff coefficient quotient shift

end QuantumAlg.NumberTheory.SharedEEA.ScanGeometry
