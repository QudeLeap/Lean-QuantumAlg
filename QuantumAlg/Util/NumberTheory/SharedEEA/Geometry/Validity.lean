/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Geometry
import Mathlib.Data.BitVec

/-! # Complete positive-window predicates, including the exact-capacity small widths -/

namespace QuantumAlg.NumberTheory.SharedEEA.ScanGeometry

/-- All widths at least two have room for the full physical window in the scan address alone. -/
lemma target_lt_address (width : Nat) (large : 2 ≤ width) :
    width + 3 < 2 ^ ScanMetadata.addressWidth width := by
  have size : 2 ≤ width.size := by
    have monotone := Nat.size_le_size large
    have two : (2 : Nat).size = 2 := by decide
    rwa [two] at monotone
  have power : 4 ≤ 2 ^ width.size := Nat.pow_le_pow_right (n := 2) (i := 2) (by decide) size
  have range := Nat.lt_size_self width
  rw [ScanMetadata.addressWidth, Nat.pow_succ]
  omega

/-- The complete carry bit is retained when testing a positive bounded physical length. -/
lemma full_validity {bits : Nat} (length : Nat) (carry : Bool) (address : BitVec bits) :
    decide (0 < (BitVec.cons carry address).toNat ∧
        (BitVec.cons carry address).toNat ≤ length) =
      ((!carry && decide (0 < address.toNat ∧ address.toNat ≤ length)) ^^
        (carry && decide (2 ^ bits + address.toNat ≤ length))) := by
  have positive : 0 < 2 ^ bits + address.toNat := by
    have := Nat.two_pow_pos bits
    omega
  simp only [BitVec.toNat_cons', Nat.shiftLeft_eq]
  cases carry with
  | false =>
      simp only [Bool.toNat_false, Nat.zero_mul, Nat.zero_add, Bool.not_false,
        Bool.true_and, Bool.false_and, Bool.xor_false]
  | true =>
      simp only [Bool.toNat_true, Nat.one_mul, positive, true_and, Bool.not_true,
        Bool.false_and, Bool.true_and, Bool.false_xor]

end QuantumAlg.NumberTheory.SharedEEA.ScanGeometry
