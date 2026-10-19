/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Remainder.BlockLaws

/-!
# Complete remainder reassembly after the actual native arithmetic block

The selected arithmetic excludes the final shift bits of the shared words
[LYL+26, sec_EEA/sub_regshare.tex:263-278]. The lower physical region of
Work1 is therefore its actual high TTK operand followed by its arbitrary
low suffix. The native subtraction, Sign complement, and add-back retain
that suffix and the complete preceding coefficient/quotient prefix
[LYL+26, sec_EEA/sub_opt.tex:43-48].

This owner proves the complete finite Work1 reconstruction and the full
natural remainder subtraction at the real binary scale. Neither equation
requires the suffix to be zero. The Sign before exchange is exactly the
weak comparison against the full shifted threshold, including equality.
The later quotient-bit exchange and field shrink are separate operations;
no early truncation or replacement execution is introduced here.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.RemainderReassembly

noncomputable section

open ArithmeticWindowRegisters ArithmeticWindowLaws
open NumberTheory.SharedEEA

/-- The complete original lower remainder region, including the unchanged binary suffix. -/
def remainderWord {width : Nat} (selected : Window width) (state : Registers width) :
    BitVec (selected.length + selected.below) :=
  state.firstWord.extractLsb' 0 (selected.length + selected.below)

/-- Literal low physical bits excluded from the selected TTK arithmetic. -/
def suffixWord {width : Nat} (selected : Window width) (state : Registers width) :
    BitVec selected.below :=
  state.firstWord.extractLsb' 0 selected.below

/-- Adjacent physical slices reassemble the complete remainder exactly at the bit level. -/
lemma remainderWord_eq {width : Nat} (selected : Window width) (state : Registers width) :
    remainderWord selected state = targetWord selected state ++ suffixWord selected state := by
  rw [targetWord, wordEquiv_window]
  exact (BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)).symm

/-- The actual upper TTK operand and arbitrary low suffix have the precise binary scale. -/
lemma remainder_toNat {width : Nat} (selected : Window width) (state : Registers width) :
    (remainderWord selected state).toNat =
      (targetWord selected state).toNat * 2 ^ selected.below +
        (suffixWord selected state).toNat := by
  rw [remainderWord_eq, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt (suffixWord selected state).isLt,
    Nat.shiftLeft_eq]

/-- Dividing the complete physical remainder by its scale gives the actual upper window. -/
lemma target_toNat {width : Nat} (selected : Window width) (state : Registers width) :
    (targetWord selected state).toNat =
      (remainderWord selected state).toNat / 2 ^ selected.below := by
  calc
    _ = (suffixWord selected state).toNat / 2 ^ selected.below +
        (targetWord selected state).toNat := by
      rw [Nat.div_eq_of_lt (suffixWord selected state).isLt, Nat.zero_add]
    _ = ((suffixWord selected state).toNat +
        (targetWord selected state).toNat * 2 ^ selected.below) / 2 ^ selected.below :=
      (Nat.add_mul_div_right _ _ (Nat.two_pow_pos selected.below)).symm
    _ = _ := congrArg (fun value => value / 2 ^ selected.below)
      ((Nat.add_comm _ _).trans (remainder_toNat selected state).symm)

/-- The unchanged suffix is exactly the complete remainder modulo the real binary scale. -/
lemma suffix_toNat {width : Nat} (selected : Window width) (state : Registers width) :
    (suffixWord selected state).toNat =
      (remainderWord selected state).toNat % 2 ^ selected.below := by
  rw [remainder_toNat, Nat.mul_add_mod_self_right,
    Nat.mod_eq_of_lt (suffixWord selected state).isLt]

/-- Every low bit of the actual remainder is retained, including arbitrary nonzero suffixes. -/
lemma source_suffix {width : Nat} (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3) :
    let selected := RemainderBlockLaws.window state fits
    suffixWord selected (ArithmeticBlocks.remainderSource state) = suffixWord selected state := by
  dsimp only
  let selected := RemainderBlockLaws.window state fits
  have same := congrArg (fun value : Complement selected => value.1.2)
    (RemainderBlockLaws.source_complement state first second fits)
  change (wordEquiv selected (ArithmeticBlocks.remainderSource state).firstWord).2.2 =
    (wordEquiv selected state.firstWord).2.2 at same
  exact (wordEquiv_below selected (ArithmeticBlocks.remainderSource state).firstWord).symm.trans
    (same.trans (wordEquiv_below selected state.firstWord))

/-- The actual entire Work1 word retains its prefix and suffix around the corrected upper window. -/
lemma source_firstWord {width : Nat} (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true)
    (zeroSign : state.flags.sign = false)
    (divisor : state.divisorLength ≠ 0)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3) :
    let selected := RemainderBlockLaws.window state fits
    (ArithmeticBlocks.remainderSource state).firstWord = (wordEquiv selected).symm
      ((wordEquiv selected state.firstWord).1,
        (SignedDivision.corrected (targetWord selected state) (sourceWord selected state),
          (wordEquiv selected state.firstWord).2.2)) := by
  dsimp only
  let selected := RemainderBlockLaws.window state fits
  have same := RemainderBlockLaws.source_complement state first second fits
  apply (wordEquiv selected).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · exact congrArg (fun value : Complement selected => value.1.1) same
  · apply Prod.ext
    · exact RemainderBlockLaws.source_target state first second zeroSign divisor fits
    · exact congrArg (fun value : Complement selected => value.1.2) same

/-- Full remainder arithmetic follows from the real high subtraction and preserved low bits. -/
lemma source_remainder_toNat {width : Nat} (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true)
    (zeroSign : state.flags.sign = false)
    (divisor : state.divisorLength ≠ 0)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3) :
    let selected := RemainderBlockLaws.window state fits
    let remainder := (remainderWord selected state).toNat
    let threshold := (sourceWord selected state).toNat * 2 ^ selected.below
    (remainderWord selected (ArithmeticBlocks.remainderSource state)).toNat =
      if threshold ≤ remainder then remainder - threshold else remainder := by
  dsimp only
  let selected := RemainderBlockLaws.window state fits
  rw [remainder_toNat selected (ArithmeticBlocks.remainderSource state),
    RemainderBlockLaws.source_target state first second zeroSign divisor fits,
    source_suffix state first second fits, suffix_toNat selected state]
  exact DivisionScale.word_corrected_reassemble (targetWord selected state)
    (sourceWord selected state) (remainderWord selected state).toNat selected.below
    (target_toNat selected state)

/-- The actual Sign digit compares the complete remainder with the complete shifted threshold. -/
lemma source_sign {width : Nat} (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true)
    (zeroSign : state.flags.sign = false)
    (divisor : state.divisorLength ≠ 0)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3) :
    let selected := RemainderBlockLaws.window state fits
    (ArithmeticBlocks.remainderSource state).flags.sign =
      decide ((sourceWord selected state).toNat * 2 ^ selected.below ≤
        (remainderWord selected state).toNat) := by
  dsimp only
  let selected := RemainderBlockLaws.window state fits
  rw [RemainderBlockLaws.source_sign state first second zeroSign divisor fits,
    target_toNat selected state]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact DivisionScale.comparison
    (remainderWord selected state).toNat (sourceWord selected state).toNat selected.below

/-- The emitted native block, on its internal clean control, performs the same full subtraction. -/
lemma native_remainder_toNat (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = false)
    (second : state.flags.second = true) (zeroSign : state.flags.sign = false)
    (divisor : state.divisorLength ≠ 0)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3) :
    let selected := RemainderBlockLaws.window state fits
    let remainder := (remainderWord selected state).toNat
    let threshold := (sourceWord selected state).toNat * 2 ^ selected.below
    (remainderWord selected (ArithmeticBlocks.remainderStep width state)).toNat =
      if threshold ≤ remainder then remainder - threshold else remainder := by
  rw [ArithmeticBlocks.remainderStep_eq_source width state clean]
  exact source_remainder_toNat state first second zeroSign divisor fits

end

end QuantumAlg.MAU.Inversion.SharedEEA.RemainderReassembly
