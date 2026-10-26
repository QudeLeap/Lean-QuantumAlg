/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Data.Nat.Bitwise
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Parameters
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Correction.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Sparse.Readout

/-! # Full-frame equivalence of the paid low-bit CNOT on the proved even branch -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling.Correction

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

private def lowWordBit (length : Nat) (positive : 0 < length) :
    EncodedBit (BinaryLabelEncoding.finIdentity length) :=
  BinaryLabelEncoding.finIdentityBit length (WireAddress.littleEndianWire ⟨0, positive⟩)

private lemma lowWordBit_flip_value (length : Nat) (positive : 0 < length)
    (word : Fin (2 ^ length)) :
    ((lowWordBit length positive).flip word).val = word.val ^^^ 1 := by
  change word.val ^^^ 2 ^ (WireAddress.bitIndex
    (WireAddress.littleEndianWire (⟨0, positive⟩ : Fin length))).val = word.val ^^^ 1
  rw [WireAddress.bitIndex_littleEndianWire]
  rfl

private lemma lowWordBit_flip_even (length : Nat) (positive : 0 < length)
    (word : Fin (2 ^ length)) (even : word.val % 2 = 0) :
    (lowWordBit length positive).flip word = Nat.FixedWidth.wordIncrement length word := by
  have value : ((lowWordBit length positive).flip word).val = word.val + 1 :=
    (lowWordBit_flip_value length positive word).trans
      (Nat.xor_one_of_even (Nat.even_iff.mpr even))
  have fits : word.val + 1 < 2 ^ length := value ▸
    ((lowWordBit length positive).flip word).isLt
  exact Fin.ext (value.trans (Nat.mod_eq_of_lt fits).symm)

private lemma full_suffix_word (state : Registers) :
    suffixWordStep width state =
      if state.2 then ((state.1.1, Nat.FixedWidth.wordIncrement width state.1.2), state.2)
      else state := by
  simp only [suffixWordStep, Nat.sub_self, Nat.pow_zero, Nat.FixedWidth.wordIncrement]

private lemma first_step_eq_word (state : Registers)
    (even : state.2 = true → state.1.2.val % 2 = 0) :
    cnotStep reductionBit targetLow state = suffixWordStep width state := by
  have actual : cnotStep reductionBit targetLow state =
      if state.2 then
        ((state.1.1, (lowWordBit width (by decide)).flip state.1.2), state.2) else state := rfl
  have pure :
      (if state.2 then
        ((state.1.1, (lowWordBit width (by decide)).flip state.1.2), state.2) else state) =
      (if state.2 then
        ((state.1.1, Nat.FixedWidth.wordIncrement width state.1.2), state.2) else state) := by
    by_cases selected : state.2 = true
    · rw [if_pos selected, if_pos selected]
      exact congrArg (fun word : Word => ((state.1.1, word), state.2))
        (lowWordBit_flip_even width (by decide) state.1.2 (even selected))
    · rw [if_neg selected, if_neg selected]
  exact actual.trans (pure.trans (full_suffix_word state).symm)

/-- On the derived selected-even branch, every original word, flag and dirty bit agrees
with the complete four-suffix correction. No assumption is made on a disabled target. -/
lemma correctionStep_eq_sparseComplement (state : Registers)
    (even : state.2 = true → state.1.2.val % 2 = 0) :
    correctionStep state = sparseComplementStep state := by
  have first := (first_step_eq_word state even).trans
    (suffixIncrementStep_eq_wordStep width le_rfl state).symm
  exact congrArg
    (fun next : Registers =>
      stepList (suffixIncrementGates 160 (by decide)).reverse
        (stepList (suffixIncrementGates 64 (by decide)).reverse
          (suffixIncrementStep 32 (by decide) next))) first

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling.Correction
