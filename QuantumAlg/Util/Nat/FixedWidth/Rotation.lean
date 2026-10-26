/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Modular.NearPower
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.BitVec

/-! # Numeric readout of one actual cyclic binary rotation -/

namespace QuantumAlg.Nat.FixedWidth.Rotation

private lemma even_or_low_bit (value bit : Nat) (even : value % 2 = 0) (small : bit < 2) :
    value ||| bit = value + bit := by
  have split : 2 * (value / 2) = value := by
    have division := Nat.mod_add_div value 2
    omega
  have packed := Nat.two_pow_add_eq_or_of_lt (i := 1) small (value / 2)
  change 2 * (value / 2) + bit = 2 * (value / 2) ||| bit at packed
  rw [split] at packed
  exact packed.symm

/-- The low bit receives the old top bit while all other bits double modulo the capacity. -/
lemma rotateLeft_one_toNat {width : Nat} (wide : 2 ≤ width) (value : BitVec width) :
    (value.rotateLeft 1).toNat = NearPower.rotatedWord (2 ^ width) value.toNat := by
  have capacity : 2 ^ width = 2 * 2 ^ (width - 1) := by
    have split : width = width - 1 + 1 := by omega
    calc
      2 ^ width = 2 ^ (width - 1 + 1) := congrArg (fun exponent => 2 ^ exponent) split
      _ = 2 * 2 ^ (width - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have positive := Nat.two_pow_pos (width - 1)
  have bounded := value.isLt
  have topSmall : value.toNat / 2 ^ (width - 1) < 2 :=
    (Nat.div_lt_iff_lt_mul positive).mpr (by omega)
  have top : value.toNat / 2 ^ (width - 1) =
      if 2 ^ width ≤ 2 * value.toNat then 1 else 0 := by
    by_cases selected : 2 ^ width ≤ 2 * value.toNat
    · rw [if_pos selected]
      have lower : 1 ≤ value.toNat / 2 ^ (width - 1) :=
        (Nat.le_div_iff_mul_le positive).mpr (by omega)
      omega
    · rw [if_neg selected]
      exact Nat.div_eq_of_lt (by omega)
  have even : ((2 * value.toNat) % 2 ^ width) % 2 = 0 := by
    rw [Nat.mod_mod_of_dvd _ ⟨2 ^ (width - 1), capacity⟩]
    simp only [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  rw [BitVec.toNat_rotateLeft, Nat.mod_eq_of_lt (by omega : 1 < width),
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  change ((value.toNat * 2) % 2 ^ width) ||| value.toNat / 2 ^ (width - 1) = _
  rw [Nat.mul_comm value.toNat 2, even_or_low_bit _ _ even topSmall, top]
  rfl

/-- The original top bit becomes the low bit used by the actual even correction. -/
lemma rotateLeft_one_low {width : Nat} (wide : 2 ≤ width) (value : BitVec width) :
    (value.rotateLeft 1).getLsbD 0 = decide (2 ^ width ≤ 2 * value.toNat) := by
  rw [BitVec.getLsbD_rotateLeft_of_le (by omega : 1 < width)]
  change value.getLsbD (width - 1) = decide (2 ^ width ≤ 2 * value.toNat)
  rw [← BitVec.msb_eq_getLsbD_last]
  apply Bool.eq_iff_iff.mpr
  rw [BitVec.msb_eq_true_iff_two_mul_ge, decide_eq_true_eq]

end QuantumAlg.Nat.FixedWidth.Rotation
