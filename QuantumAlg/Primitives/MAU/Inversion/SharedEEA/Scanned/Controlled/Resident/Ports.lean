/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Resident

/-! # Actual resident payload and saved systems at both full inversion boundaries -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledResident

noncomputable section

def work1 {width : Nat} (state : ControlledResidentFrame.Data width) : Fin (2 ^ width) :=
  BitVec.equivFin (state.1.1.1.firstWord.reverse.setWidth width)

/-- The full original n-bit work payload is genuinely zero after this actual forward. -/
lemma result_work1_zero (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) (numerator : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : ControlledResidentFrame.Flags) :
    work1 (result modulus input positive bounded numerator pool flags) = 0 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  change (BitVec.setWidth modulus.size
    (result modulus input positive bounded numerator pool flags).1.1.1.firstWord.reverse).getLsbD
      index.val = (0 : Nat).testBit index.val
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_reverse]
  simp only [index.isLt, decide_true, Bool.true_and, Nat.zero_testBit]
  exact result_large_bit modulus input coprime positive bounded numerator pool flags index

lemma initial_numerator (modulus : Nat) (input numerator : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : ControlledResidentFrame.Flags) :
    (initial modulus input numerator pool flags).1.2 = numerator := rfl

lemma result_numerator (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags) :
    (result modulus input positive bounded numerator pool flags).1.2 = numerator := rfl

lemma initial_pool (modulus : Nat) (input numerator : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : ControlledResidentFrame.Flags) :
    (initial modulus input numerator pool flags).1.1.2 = pool := rfl

lemma result_pool (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags) :
    (result modulus input positive bounded numerator pool flags).1.1.2 = pool := rfl

lemma initial_flags (modulus : Nat) (input numerator : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : ControlledResidentFrame.Flags) :
    (initial modulus input numerator pool flags).2 = flags := rfl

lemma result_flags (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags) :
    (result modulus input positive bounded numerator pool flags).2 = flags := rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledResident
