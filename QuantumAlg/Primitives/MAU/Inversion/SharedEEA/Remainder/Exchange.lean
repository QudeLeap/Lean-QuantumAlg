/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.SignQuotient

/-!
# Actual phase-two Sign exchange before remainder-field shrink

The baseline increments quotient length before exchanging Sign at its
new last position [LYL+26, sec_EEA/sub_regshare.tex:281-287]. The actual
optimized native order exchanges at the equivalent old natural position
`lt + lq + 1` and then executes the real quotient-length increment.

The equations below concern the already emitted selector and incrementer.
They retain every lower remainder bit, put the actual incoming Sign into
the new quotient position, and return that position's old bit in Sign.
The local next-capacity condition proves that this old bit is zero; the
complete division trajectory must supply it internally. Nothing assumes
that the old remainder already fits the shorter region before subtraction.
Zero-bit next remainder regions are included, without a different circuit.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.RemainderExchange

noncomputable section

open EncodedBit

private lemma distinct_word {width : Nat} (left right : Fin (width + 3))
    (different : left ≠ right) :
    (firstWordBit width left).wire ≠ (firstWordBit width right).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [firstWordBit_wire, firstWordBit_wire] at values
  exact different (Fin.ext values)

/-- Every original Work1 bit except the actual selected quotient position is unchanged. -/
lemma exchange_other (width : Nat) (selected observed : Fin (width + 3))
    (different : selected ≠ observed) (state : Registers width) :
    (SelectionSwap.exchange width selected state).firstWord.getMsbD observed.val =
      state.firstWord.getMsbD observed.val := by
  calc
    _ = (firstWordBit width observed).get (SelectionSwap.exchange width selected state) :=
      (firstWordBit_get width observed _).symm
    _ = (firstWordBit width observed).get state :=
      swapStep_get_observed_of_swap_ne (signBit width) (firstWordBit width selected)
        (firstWordBit width observed) (SelectionSwap.sign_word width selected)
        (SelectionSwap.sign_word width observed) (distinct_word selected observed different) state
    _ = _ := firstWordBit_get width observed state

private lemma physical_lsb {width : Nat} (word : BitVec (width + 3)) (bit : Nat)
    (within : bit < width + 3) :
    word.getLsbD bit = word.getMsbD (width + 3 - 1 - bit) := by
  have indexWithin : width + 3 - 1 - bit < width + 3 := by omega
  have reverse : width + 3 - 1 - (width + 3 - 1 - bit) = bit := by omega
  simp only [BitVec.getMsbD_eq_getLsbD, indexWithin, decide_true, Bool.true_and, reverse]

/-- The actual swap leaves all lower remainder bits, including a zero-width region, intact. -/
lemma exchange_low (width : Nat) (selected : Fin (width + 3)) (state : Registers width) :
    (SelectionSwap.exchange width selected state).firstWord.setWidth
        (width + 3 - 1 - selected.val) =
      state.firstWord.setWidth (width + 3 - 1 - selected.val) := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit within
  simp only [BitVec.getLsbD_setWidth, within, decide_true, Bool.true_and]
  have fullWithin : bit < width + 3 := by omega
  let observed : Fin (width + 3) := ⟨width + 3 - 1 - bit, by omega⟩
  have different : selected ≠ observed := by
    intro same
    have values := congrArg Fin.val same
    change selected.val = width + 3 - 1 - bit at values
    omega
  exact (physical_lsb _ bit fullWithin).trans
    ((exchange_other width selected observed different state).trans
      (physical_lsb state.firstWord bit fullWithin).symm)

/-- The actual exchanged lower word is incoming Sign followed by the complete retained remainder. -/
lemma exchange_word (width : Nat) (selected : Fin (width + 3)) (state : Registers width) :
    (SelectionSwap.exchange width selected state).firstWord.setWidth
        (width + 3 - 1 - selected.val + 1) =
      BitVec.cons state.flags.sign
        (state.firstWord.setWidth (width + 3 - 1 - selected.val)) := by
  have high := SelectionSwap.exchange_wordBit width selected state
  rw [BitVec.getMsbD_eq_getLsbD] at high
  simp only [selected.isLt, decide_true, Bool.true_and] at high
  rw [BitVec.setWidth_succ, exchange_low, high]

/-- The old highest remainder bit, not an assumed zero, is returned to the actual Sign field. -/
lemma exchange_sign (width : Nat) (selected : Fin (width + 3)) (state : Registers width) :
    (SelectionSwap.exchange width selected state).flags.sign =
      (state.firstWord.setWidth (width + 3 - 1 - selected.val + 1)).msb := by
  rw [SelectionSwap.exchange_sign, BitVec.msb_setWidth'']
  simp only [BitVec.getMsbD_eq_getLsbD, selected.isLt, decide_true, Bool.true_and]

private lemma selected_source (width : Nat) (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true)
    (within : state.coefficientLength.toNat + state.quotientLength.toNat + 1 < width + 3) :
    SelectionSchedule.sourceStep width state = SelectionSwap.exchange width
      ⟨state.coefficientLength.toNat + state.quotientLength.toNat + 1, within⟩ state := by
  unfold SelectionSchedule.sourceStep
  simp only [first, Bool.false_eq_true, if_false, dif_pos within, SelectionKey.phaseSelected,
    second, Bool.false_xor, if_true]

/-- The real selector and length increment write incoming Sign at the actual source position. -/
lemma source_word (width : Nat) (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true)
    (within : state.coefficientLength.toNat + state.quotientLength.toNat + 1 < width + 3) :
    let nextWidth := width + 3 - 1 -
      (state.coefficientLength.toNat + state.quotientLength.toNat + 1)
    (SignQuotient.sourceStep width state).firstWord.setWidth (nextWidth + 1) =
      BitVec.cons state.flags.sign (state.firstWord.setWidth nextWidth) := by
  dsimp only
  change (SelectionSchedule.sourceStep width state).firstWord.setWidth _ = _
  rw [selected_source width state first second within]
  exact exchange_word width
    ⟨state.coefficientLength.toNat + state.quotientLength.toNat + 1, within⟩ state

/-- The actual source-selected Sign output is exactly the previous top remainder bit. -/
lemma source_sign (width : Nat) (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true)
    (within : state.coefficientLength.toNat + state.quotientLength.toNat + 1 < width + 3) :
    let nextWidth := width + 3 - 1 -
      (state.coefficientLength.toNat + state.quotientLength.toNat + 1)
    (SignQuotient.sourceStep width state).flags.sign =
      (state.firstWord.setWidth (nextWidth + 1)).msb := by
  dsimp only
  change (SelectionSchedule.sourceStep width state).flags.sign = _
  rw [selected_source width state first second within]
  exact exchange_sign width _ state

/-- An internally proved next-remainder capacity clears Sign only after the actual subtraction. -/
lemma source_sign_clear (width : Nat) (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true)
    (within : state.coefficientLength.toNat + state.quotientLength.toNat + 1 < width + 3)
    (nextFits :
      (state.firstWord.setWidth (width + 3 - 1 -
        (state.coefficientLength.toNat + state.quotientLength.toNat + 1) + 1)).toNat <
          2 ^ (width + 3 - 1 -
            (state.coefficientLength.toNat + state.quotientLength.toNat + 1))) :
    (SignQuotient.sourceStep width state).flags.sign = false := by
  rw [source_sign width state first second within, BitVec.msb_eq_decide, Nat.add_sub_cancel]
  exact decide_eq_false (Nat.not_le.mpr nextFits)

/-- The already emitted complete native Sign/quotient block has the exact finite-word equation. -/
lemma native_word (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = false)
    (second : state.flags.second = true)
    (within : state.coefficientLength.toNat + state.quotientLength.toNat + 1 < width + 3) :
    let nextWidth := width + 3 - 1 -
      (state.coefficientLength.toNat + state.quotientLength.toNat + 1)
    (SignQuotient.step width state).firstWord.setWidth (nextWidth + 1) =
      BitVec.cons state.flags.sign (state.firstWord.setWidth nextWidth) := by
  rw [SignQuotient.step_eq_sourceStep width state clean]
  exact source_word width state first second within

end

end QuantumAlg.MAU.Inversion.SharedEEA.RemainderExchange
