/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Geometry.Word

/-!
# Complete finite coefficient lengths in both source phases

The phase-three length is coefficient plus one; the phase-four length
is physical width minus complete divisor and shift. The temporary high
carry distinguishes negative lengths from valid physical windows on
every finite metadata label, independently of trajectory invariants.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.ScanGeometry

/-- Both full-word source lengths retain every original finite metadata bit. -/
def coefficientWord {width : Nat} (deshift : Bool)
    (coefficient divisor shift : BitVec width.size) : BitVec (fullWidth width) :=
  if deshift then BitVec.ofNat (fullWidth width) (width + 3) - extend divisor - extend shift
  else extend coefficient + 1

/-- Exact natural residue of either complete finite source length. -/
lemma coefficientWord_toNat {width : Nat} (deshift : Bool)
    (coefficient divisor shift : BitVec width.size) :
    (coefficientWord deshift coefficient divisor shift).toNat =
      if deshift then residue (2 ^ fullWidth width) (width + 3)
        (divisor.toNat + shift.toNat) else coefficient.toNat + 1 := by
  have capacity := target_lt width
  have coefficientBound := coefficient.isLt
  have divisorBound := divisor.isLt
  have shiftBound := shift.isLt
  have positive := Nat.two_pow_pos width.size
  have sumBound : divisor.toNat + shift.toNat < 2 ^ fullWidth width := by
    simp only [fullWidth, Nat.pow_succ]
    omega
  cases deshift with
  | false =>
      have small : coefficient.toNat + 1 < 2 ^ fullWidth width := by
        simp only [fullWidth, Nat.pow_succ]
        omega
      simp only [coefficientWord, Bool.false_eq_true, if_false, BitVec.toNat_add,
        extend_toNat]
      change (coefficient.toNat + 1 % 2 ^ fullWidth width) % 2 ^ fullWidth width =
        coefficient.toNat + 1
      have one : 1 % 2 ^ fullWidth width = 1 := Nat.mod_eq_of_lt (by omega)
      rw [one, Nat.mod_eq_of_lt small]
  | true =>
      have sum : (extend divisor + extend shift).toNat = divisor.toNat + shift.toNat := by
        rw [BitVec.toNat_add, extend_toNat, extend_toNat, Nat.mod_eq_of_lt sumBound]
      simp only [coefficientWord, if_true]
      rw [BitVec.sub_sub, BitVec.toNat_sub', sum, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt capacity]
      unfold residue
      apply congrArg (fun value : Nat => value % 2 ^ fullWidth width)
      omega

/-- A full-carry positive test admits precisely the untruncated positive physical lengths. -/
lemma coefficientWord_positive_iff {width : Nat} (deshift : Bool)
    (coefficient divisor shift : BitVec width.size) :
    (0 < (coefficientWord deshift coefficient divisor shift).toNat ∧
      (coefficientWord deshift coefficient divisor shift).toNat ≤ width + 3) ↔
      if deshift then divisor.toNat + shift.toNat < width + 3
      else coefficient.toNat + 1 ≤ width + 3 := by
  rw [coefficientWord_toNat]
  cases deshift with
  | false => simp
  | true =>
      simp only [if_true]
      apply residue_positive_iff _ _ _ (target_lt width)
      have left := divisor.isLt
      have right := shift.isLt
      have positive := Nat.two_pow_pos width.size
      simp only [fullWidth, Nat.pow_succ]
      omega

end QuantumAlg.NumberTheory.SharedEEA.ScanGeometry
