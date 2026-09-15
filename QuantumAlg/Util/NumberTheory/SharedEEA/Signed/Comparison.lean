/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Signed.Coefficient

/-!
# Complete finite-word comparison by the actual signed instruction sequence

The optimized coefficient comparison subtracts the low source word,
complements Sign, and adds the source into the complete signed target
[LYL+26, sec_EEA/sub_opt.tex:61-66]. On any two finite words, those operations
retain the entire target and xor their weak unsigned comparison into Sign.
Equality and zero-bit words are included, with arbitrary incoming Sign.

This exact arithmetic identity can support a native comparison only after
the selected physical operands are proved to contain the full compared
integers. It does not justify dropping high bits from a rotated coefficient.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.SignedComparison

/-- Literal low subtraction, Sign complement, and signed addition, for arbitrary finite inputs. -/
def instruction {width : Nat} (value coefficient : BitVec width) (sign : Bool) :
    BitVec (width + 1) :=
  BitVec.cons (!sign) (value - coefficient) + coefficient.setWidth (width + 1)

/-- The actual instructions retain the complete low word and xor the weak comparison into Sign. -/
theorem instruction_eq {width : Nat} (value coefficient : BitVec width) (sign : Bool) :
    instruction value coefficient sign =
      BitVec.cons (sign ^^ decide (coefficient.toNat ≤ value.toNat)) value := by
  have coefficientNat : (coefficient.setWidth (width + 1)).toNat = coefficient.toNat :=
    BitVec.toNat_setWidth_of_le (by omega)
  have valueBound := value.isLt
  have coefficientBound := coefficient.isLt
  have extendedBound : value.toNat < 2 ^ (width + 1) :=
    valueBound.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  have signedBound : 2 ^ width + value.toNat < 2 ^ (width + 1) := by
    rw [Nat.pow_succ]
    omega
  apply BitVec.eq_of_toNat_eq
  by_cases selected : coefficient.toNat ≤ value.toNat
  · have ordered : coefficient ≤ value := by
      simpa only [BitVec.le_def] using selected
    rw [instruction, BitVec.toNat_add, BitVec.toNat_cons',
      BitVec.toNat_sub_of_le ordered, coefficientNat, BitVec.toNat_cons', decide_eq_true selected]
    cases sign with
    | false =>
        simp only [Bool.not_false, Bool.false_xor, Bool.toNat_true, Nat.shiftLeft_eq, Nat.one_mul]
        have assembled : 2 ^ width + (value.toNat - coefficient.toNat) + coefficient.toNat =
            2 ^ width + value.toNat := by omega
        rw [assembled, Nat.mod_eq_of_lt signedBound]
    | true =>
        simp only [Bool.not_true, Bool.xor_self, Bool.toNat_false, Nat.shiftLeft_eq,
          Nat.zero_mul, Nat.zero_add]
        rw [Nat.sub_add_cancel selected, Nat.mod_eq_of_lt extendedBound]
  · have borrowed : value.toNat < coefficient.toNat := by omega
    have ordered : value < coefficient := by
      simpa only [BitVec.lt_def] using borrowed
    rw [instruction, BitVec.toNat_add, BitVec.toNat_cons',
      BitVec.toNat_sub_of_lt ordered, coefficientNat, BitVec.toNat_cons', decide_eq_false selected]
    cases sign with
    | false =>
        simp only [Bool.not_false, Bool.xor_false, Bool.toNat_true, Bool.toNat_false,
          Nat.shiftLeft_eq, Nat.one_mul, Nat.zero_mul, Nat.zero_add]
        have assembled : 2 ^ width + (2 ^ width - (coefficient.toNat - value.toNat)) +
            coefficient.toNat = 2 ^ (width + 1) + value.toNat := by
          rw [Nat.pow_succ]
          omega
        rw [assembled, Nat.add_mod_left, Nat.mod_eq_of_lt extendedBound]
    | true =>
        simp only [Bool.not_true, Bool.xor_false, Bool.toNat_false, Bool.toNat_true,
          Nat.shiftLeft_eq, Nat.zero_mul, Nat.zero_add, Nat.one_mul]
        have assembled : 2 ^ width - (coefficient.toNat - value.toNat) + coefficient.toNat =
            2 ^ width + value.toNat := by omega
        rw [assembled, Nat.mod_eq_of_lt signedBound]

/-- No original target bit is changed by the complete comparison instruction. -/
theorem instruction_low {width : Nat} (value coefficient : BitVec width) (sign : Bool) :
    (instruction value coefficient sign).setWidth width = value := by
  rw [instruction_eq, BitVec.setWidth_cons]

/-- The output Sign is the exact weak unsigned comparison xor, including equality. -/
theorem instruction_sign {width : Nat} (value coefficient : BitVec width) (sign : Bool) :
    (instruction value coefficient sign).msb =
      (sign ^^ decide (coefficient.toNat ≤ value.toNat)) := by
  rw [instruction_eq, BitVec.msb_cons]

/-- A zero-width comparison still correctly complements Sign because both words equal zero. -/
theorem empty_instruction (sign : Bool) :
    instruction (0#0) (0#0) sign = BitVec.cons (!sign) (0#0) := by
  rw [instruction_eq]
  cases sign <;> rfl

end QuantumAlg.NumberTheory.SharedEEA.SignedComparison
