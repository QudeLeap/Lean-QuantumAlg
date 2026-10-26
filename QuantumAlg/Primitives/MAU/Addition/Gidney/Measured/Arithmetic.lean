/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.Binary.Arithmetic
import Mathlib.Data.BitVec

/-!
# Carry recovery from the complemented finite sum

The phase repair recomputes the original carries from the complemented output
and the same offset. This is the finite-word form of the carry-negation
identity [G25, main.tex:209-239]. The offset can be the value selected by an
arbitrary quantum-control label; no control-dependent measurement is skipped.
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured

/-- The streaming carry is one affine-control Toffoli followed by the offset xor. -/
lemma carry_eq_affine_toffoli (input offset incoming : Bool) :
    (((input ^^ offset) && (incoming ^^ offset)) ^^ offset) =
      Bool.carry input offset incoming := by
  cases input <;> cases offset <;> cases incoming <;> rfl

/-- The first carry has no incoming carry and retains the arbitrary dirty output bit. -/
lemma first_carry_xor (input offset dirty : Bool) :
    ((dirty ^^ offset) ^^ ((input ^^ offset) && offset)) =
      (dirty ^^ (input && offset)) := by
  cases input <;> cases offset <;> cases dirty <;> rfl

/-- The paired native Toffolis cancel the unknown predecessor dirty value exactly. -/
lemma dirty_carry_xor (input offset incoming previous dirty : Bool) :
    (((dirty ^^ ((input ^^ offset) && previous)) ^^ offset) ^^
        ((input ^^ offset) && ((previous ^^ incoming) ^^ offset))) =
      (dirty ^^ Bool.carry input offset incoming) := by
  cases input <;> cases offset <;> cases incoming <;> cases previous <;> cases dirty <;> rfl

/-- The same incoming carry propagates through the complemented local sum. -/
lemma carry_complement_xor (input offset incoming : Bool) :
    Bool.carry (!(input ^^ offset ^^ incoming)) offset incoming =
      Bool.carry input offset incoming := by
  cases input <;> cases offset <;> cases incoming <;> rfl

/-- A retained sum bit is the usual input/offset/carry xor before complementing. -/
lemma complemented_sum_bit {width : Nat} (input offset : BitVec width)
    (index : Nat) (inside : index < width) :
    (~~~(input + offset)).toNat.testBit index =
      !(input.toNat.testBit index ^^ offset.toNat.testBit index ^^
        Nat.BinaryArithmetic.natAddCarry input.toNat offset.toNat index) := by
  rw [BitVec.testBit_toNat, BitVec.getLsbD_not, decide_eq_true inside, Bool.true_and,
    ← BitVec.testBit_toNat, BitVec.toNat_add, Nat.testBit_mod_two_pow,
    decide_eq_true inside, Bool.true_and, Nat.BinaryArithmetic.testBit_add_eq_xor3]

/-- Every carry in the complete finite prefix is recovered from the complemented sum. -/
lemma carry_complemented_sum {width : Nat} (input offset : BitVec width)
    (index : Nat) (bounded : index ≤ width) :
    Nat.BinaryArithmetic.natAddCarry (~~~(input + offset)).toNat offset.toNat index =
      Nat.BinaryArithmetic.natAddCarry input.toNat offset.toNat index := by
  revert bounded
  induction index with
  | zero => intro _; rfl
  | succ index ih =>
      intro bounded
      rw [Nat.BinaryArithmetic.natAddCarry, Nat.BinaryArithmetic.natAddCarry,
        ih (Nat.le_of_succ_le bounded),
        complemented_sum_bit input offset index (Nat.lt_of_succ_le bounded),
        carry_complement_xor]

end QuantumAlg.MAU.Addition.Gidney.Measured
