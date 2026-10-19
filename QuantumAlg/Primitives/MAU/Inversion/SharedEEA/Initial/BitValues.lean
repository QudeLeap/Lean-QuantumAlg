/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.Frame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Input.Preparation
import Mathlib.Data.Nat.Bitwise

/-!
# Literal source initial bits at their actual physical addresses

The source initializes Work1 to `100,p`, Work2 to `000,x`, coefficient
length to one, and the phase/sign/parity bits to zero
[LYL+26, sec_EEA/sub_4phase.tex:104-117]. The actual divisor-length writer
runs after folding, so that length is initially zero as well.

These laws identify the source basis specification with the fixed bits
used by the actual auxiliary preparation. Every Work2 input bit still
reads the original unknown input value. The statements include zero-width
finite fields and impose no condition on the input's value beyond its
original finite binary carrier.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InitialBitValues

noncomputable section

open InputPreparation

/-- Every actual Work1 bit has exactly the source's fixed initial value. -/
lemma firstWord_fixed (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (index : Fin (modulus.size + 3)) :
    fixedBit modulus (firstWordBit modulus.size index).wire.val =
      (firstWordBit modulus.size index).get (InitialFrame.initial modulus input) := by
  rw [firstWordBit_wire, firstWordBit_get]
  change fixedBit modulus index.val =
    (BitVec.ofNat (modulus.size + 3) (4 * 2 ^ modulus.size + modulus)).getMsbD index.val
  rw [fixedBit, if_pos index.isLt]

/-- The actual coefficient-length field is initialized to the finite binary label one. -/
lemma coefficientLength_fixed (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (index : Fin modulus.size.size) :
    fixedBit modulus (coefficientLengthBit modulus.size index).wire.val =
      (coefficientLengthBit modulus.size index).get (InitialFrame.initial modulus input) := by
  rw [coefficientLengthBit_wire, coefficientLengthBit_get]
  have bound := index.isLt
  have afterWord : ¬2 * (modulus.size + 3) + index.val < modulus.size + 3 := by omega
  have within : 2 * (modulus.size + 3) ≤ 2 * (modulus.size + 3) + index.val ∧
      2 * (modulus.size + 3) + index.val <
        2 * (modulus.size + 3) + modulus.size.size := by omega
  change fixedBit modulus (2 * (modulus.size + 3) + index.val) =
    (BitVec.ofNat modulus.size.size 1).getMsbD index.val
  rw [fixedBit, if_neg afterWord, if_pos within, Nat.add_sub_cancel_left]

private lemma fixedBit_tail_zero (modulus wire : Nat)
    (afterCoefficient : 2 * (modulus.size + 3) + modulus.size.size ≤ wire) :
    fixedBit modulus wire = false := by
  rw [fixedBit, if_neg (by omega), if_neg (by omega)]

/-- Every actual quotient-length bit is among the prepared fixed zeros. -/
lemma quotientLength_fixed (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (index : Fin modulus.size.size) :
    fixedBit modulus (quotientLengthBit modulus.size index).wire.val =
      (quotientLengthBit modulus.size index).get (InitialFrame.initial modulus input) := by
  rw [quotientLengthBit_wire, quotientLengthBit_get, fixedBit_tail_zero modulus _ (by omega)]
  simp [InitialFrame.initial]

/-- The real divisor-length input is zero before the native writer computes from current Work2. -/
lemma divisorLength_fixed (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (index : Fin modulus.size.size) :
    fixedBit modulus (divisorLengthBit modulus.size index).wire.val =
      (divisorLengthBit modulus.size index).get (InitialFrame.initial modulus input) := by
  rw [divisorLengthBit_wire, divisorLengthBit_get, fixedBit_tail_zero modulus _ (by omega)]
  simp [InitialFrame.initial]

/-- The complete original low shift starts at actual finite zero. -/
lemma shift_fixed (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (index : Fin modulus.size.size) :
    fixedBit modulus (shiftBit modulus.size index).wire.val =
      (shiftBit modulus.size index).get (InitialFrame.initial modulus input) := by
  rw [shiftBit_wire, shiftBit_get, fixedBit_tail_zero modulus _ (by omega)]
  simp [InitialFrame.initial]

/-- The first phase bit is an actual prepared zero. -/
lemma phase1_fixed (modulus : Nat) (input : Fin (2 ^ modulus.size)) :
    fixedBit modulus (phase1Bit modulus.size).wire.val =
      (phase1Bit modulus.size).get (InitialFrame.initial modulus input) := by
  rw [phase1Bit_wire, phase1Bit_get, fixedBit_tail_zero modulus _ (by omega)]
  rfl

/-- The second phase bit is an actual prepared zero. -/
lemma phase2_fixed (modulus : Nat) (input : Fin (2 ^ modulus.size)) :
    fixedBit modulus (phase2Bit modulus.size).wire.val =
      (phase2Bit modulus.size).get (InitialFrame.initial modulus input) := by
  rw [phase2Bit_wire, phase2Bit_get, fixedBit_tail_zero modulus _ (by omega)]
  rfl

/-- Sign is initialized internally, with no sign-value promise imposed on the caller. -/
lemma sign_fixed (modulus : Nat) (input : Fin (2 ^ modulus.size)) :
    fixedBit modulus (signBit modulus.size).wire.val =
      (signBit modulus.size).get (InitialFrame.initial modulus input) := by
  rw [signBit_wire, signBit_get, fixedBit_tail_zero modulus _ (by omega)]
  rfl

/-- Iter zero is prepared before the actual reversible fold writes its retained history. -/
lemma iteration_fixed (modulus : Nat) (input : Fin (2 ^ modulus.size)) :
    fixedBit modulus (iterationBit modulus.size).wire.val =
      (iterationBit modulus.size).get (InitialFrame.initial modulus input) := by
  rw [iterationBit_wire, iterationBit_get, fixedBit_tail_zero modulus _ (by omega)]
  rfl

/-- The fifth source control is an actually prepared zero, rather than hidden clean workspace. -/
lemma control_fixed (modulus : Nat) (input : Fin (2 ^ modulus.size)) :
    fixedBit modulus (controlBit modulus.size).wire.val =
      (controlBit modulus.size).get (InitialFrame.initial modulus input) := by
  rw [controlBit_wire, controlBit_get, fixedBit_tail_zero modulus _ (by omega)]
  rfl

/-- Each of the three real Work2 padding positions is a prepared zero above the original input. -/
lemma secondWord_padding_fixed (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (index : Fin (modulus.size + 3)) (padding : index.val < 3) :
    fixedBit modulus (secondWordBit modulus.size index).wire.val =
      (secondWordBit modulus.size index).get (InitialFrame.initial modulus input) := by
  rw [secondWordBit_wire, secondWordBit_get]
  have afterWord : ¬modulus.size + 3 + index.val < modulus.size + 3 := by omega
  have beforeLengths : ¬(2 * (modulus.size + 3) ≤ modulus.size + 3 + index.val ∧
      modulus.size + 3 + index.val < 2 * (modulus.size + 3) + modulus.size.size) := by
    have bound := index.isLt
    omega
  rw [fixedBit, if_neg afterWord, if_neg beforeLengths]
  rw [BitVec.getMsbD_eq_getLsbD]
  simp only [index.isLt, decide_true, Bool.true_and, BitVec.getLsbD,
    InitialFrame.initial_secondWord]
  have fits : input.val < 2 ^ (modulus.size + 3 - 1 - index.val) :=
    input.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  exact (Nat.testBit_eq_false_of_lt fits).symm

/-- Every remaining Work2 bit retains the original input's unknown binary value. -/
lemma secondWord_input (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (index : Fin modulus.size) :
    (secondWordBit modulus.size ⟨3 + index.val, by have bound := index.isLt; omega⟩).get
        (InitialFrame.initial modulus input) = input.val.testBit index.rev.val := by
  rw [secondWordBit_get, BitVec.getMsbD_eq_getLsbD]
  have within : 3 + index.val < modulus.size + 3 := by have bound := index.isLt; omega
  have reverse : modulus.size + 3 - 1 - (3 + index.val) = index.rev.val := by
    rw [Fin.val_rev]
    omega
  simp only [within, decide_true, Bool.true_and, BitVec.getLsbD,
    InitialFrame.initial_secondWord, reverse]

end

end QuantumAlg.MAU.Inversion.SharedEEA.InitialBitValues
