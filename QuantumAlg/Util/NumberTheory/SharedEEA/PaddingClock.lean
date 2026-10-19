/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Terminal.Padding
import all QuantumAlg.Util.NumberTheory.SharedEEA.Terminal.Tail

/-!
# Reversible counter coordinates in the actual two terminal padding bits

The first shared word has the physical order fixed by the registered
source [LYL+26, sec_EEA/sub_regshare.tex:16-23]. Its two candidate terminal
padding positions were proved zero in `TerminalPadding`. This owner
extracts those exact bits and concatenates them with the original low
counter. All other word bits remain explicit. The two coordinate maps
are inverses on every full word and counter, without a cleanliness premise.

The increment and decrement below are explicit finite arithmetic through
those exact coordinates. Their inverse laws and preservation of every
unselected word bit are proved. A conditional version uses the unchanged
divisor-length register: the active branch updates only the original low
counter, and does not assume either padding bit is zero.

This is a mathematical repair candidate for the finite counter operations
in [LYL+26, sec_EEA/sub_opt.tex:37-40,68-84]. It neither claims that the
registered source already uses these bits this way nor implements native
elementary gates. Predicate compute/uncompute, coherent placement, the
full terminal rotation/control sequence, and native resource accounting
remain separate obligations. Input-dependent high-counter history stays
in the word until the actual inverse assignments restore it.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.PaddingClock

variable {mainWidth lowWidth : Nat}

/-- Read all original main-data bits, excluding exactly the three physical tail positions. -/
def main (word : BitVec (mainWidth + 3)) : BitVec mainWidth :=
  (word.extractLsb' 1 (mainWidth + 2)).extractLsb' 2 mainWidth

/-- Read precisely the two physical padding positions, in their natural high-counter order. -/
def high (word : BitVec (mainWidth + 3)) : BitVec 2 :=
  (word.extractLsb' 1 (mainWidth + 2)).extractLsb' 0 2

/-- Keep the final physical bit separate; it is not a proposed counter position. -/
def last (word : BitVec (mainWidth + 3)) : BitVec 1 := word.extractLsb' 0 1

/-- Split the complete word and low counter into unchanged data and the combined counter. -/
def split (state : BitVec (mainWidth + 3) × BitVec lowWidth) :
    (BitVec mainWidth × BitVec 1) × BitVec (2 + lowWidth) :=
  ((main state.1, last state.1), high state.1 ++ state.2)

/-- Reassemble every physical bit from its precise source position. -/
def join (coordinates : (BitVec mainWidth × BitVec 1) × BitVec (2 + lowWidth)) :
    BitVec (mainWidth + 3) × BitVec lowWidth :=
  (((coordinates.1.1 ++ coordinates.2.extractLsb' lowWidth 2) ++ coordinates.1.2),
    coordinates.2.extractLsb' 0 lowWidth)

/-- Splitting and reassembling recovers the complete original word and low counter. -/
lemma join_split (state : BitVec (mainWidth + 3) × BitVec lowWidth) :
    join (split state) = state := by
  rcases state with ⟨word, low⟩
  simp only [join, split, main, high, last, BitVec.extractLsb'_append_eq_left,
    BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_extractLsb']

/-- Reassembling and splitting also recovers every arbitrary combined-counter coordinate. -/
lemma split_join (coordinates : (BitVec mainWidth × BitVec 1) × BitVec (2 + lowWidth)) :
    split (join coordinates) = coordinates := by
  rcases coordinates with ⟨⟨head, tail⟩, counter⟩
  simp only [join, split, main, high, last, BitVec.extractLsb'_append_eq_left,
    BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_extractLsb']

/-- An explicit wire-position equivalence; no extra register or cardinality-based cast is used. -/
def coordinatesEquiv : (BitVec (mainWidth + 3) × BitVec lowWidth) ≃
    ((BitVec mainWidth × BitVec 1) × BitVec (2 + lowWidth)) where
  toFun := split
  invFun := join
  left_inv := join_split
  right_inv := split_join

/-- Apply one actual modular increment to the combined finite counter. -/
def increment (state : BitVec (mainWidth + 3) × BitVec lowWidth) :
    BitVec (mainWidth + 3) × BitVec lowWidth :=
  join ((split state).1, (split state).2 + 1)

/-- Apply its modular inverse on the same physical high positions and original low bits. -/
def decrement (state : BitVec (mainWidth + 3) × BitVec lowWidth) :
    BitVec (mainWidth + 3) × BitVec lowWidth :=
  join ((split state).1, (split state).2 - 1)

/-- The real increment changes exactly the combined counter in the complete coordinate equation. -/
lemma split_increment (state : BitVec (mainWidth + 3) × BitVec lowWidth) :
    split (increment state) = ((split state).1, (split state).2 + 1) := split_join _

/-- The inverse changes exactly the combined counter in the opposite direction. -/
lemma split_decrement (state : BitVec (mainWidth + 3) × BitVec lowWidth) :
    split (decrement state) = ((split state).1, (split state).2 - 1) := split_join _

/-- Reverse the true combined increment on the entire original physical state. -/
lemma decrement_increment (state : BitVec (mainWidth + 3) × BitVec lowWidth) :
    decrement (increment state) = state := by
  unfold decrement
  rw [split_increment, BitVec.add_sub_cancel]
  exact join_split state

/-- The converse inverse law includes every original word and low-counter value. -/
lemma increment_decrement (state : BitVec (mainWidth + 3) × BitVec lowWidth) :
    increment (decrement state) = state := by
  unfold increment
  rw [split_decrement, BitVec.sub_add_cancel]
  exact join_split state

/-- All original main data and the separate last bit are unchanged as whole finite words. -/
lemma increment_untouched (state : BitVec (mainWidth + 3) × BitVec lowWidth) :
    main (increment state).1 = main state.1 ∧ last (increment state).1 = last state.1 := by
  have unchanged := congrArg Prod.fst (split_increment state)
  exact ⟨congrArg Prod.fst unchanged, congrArg Prod.snd unchanged⟩

/-- The inverse also preserves every main-data bit and the separate final bit. -/
lemma decrement_untouched (state : BitVec (mainWidth + 3) × BitVec lowWidth) :
    main (decrement state).1 = main state.1 ∧ last (decrement state).1 = last state.1 := by
  have unchanged := congrArg Prod.fst (split_decrement state)
  exact ⟨congrArg Prod.fst unchanged, congrArg Prod.snd unchanged⟩

/-- The combined counter has its actual modular arithmetic value, including all carry bits. -/
lemma increment_value (state : BitVec (mainWidth + 3) × BitVec lowWidth) :
    (split (increment state)).2.toNat =
      ((split state).2.toNat + 1) % 2 ^ (2 + lowWidth) := by
  rw [split_increment]
  exact TerminalTail.increment_toNat _

private lemma join_high_bit
    (coordinates : (BitVec mainWidth × BitVec 1) × BitVec (2 + lowWidth))
    (index : Nat) (within : index < 2) :
    (join coordinates).1.getMsbD (mainWidth + index) =
      (coordinates.2.extractLsb' lowWidth 2).getMsbD index := by
  have beforeTail : ¬ mainWidth + 2 ≤ mainWidth + index := by omega
  have afterMain : mainWidth ≤ mainWidth + index := by omega
  simp only [join, BitVec.getMsbD_append, if_neg beforeTail, if_pos afterMain,
    Nat.add_sub_cancel_left]

/-- Each extracted high bit is exactly its prescribed physical position in the complete word. -/
lemma high_bit (word : BitVec (mainWidth + 3)) (index : Nat) (within : index < 2) :
    word.getMsbD (mainWidth + index) = (high word).getMsbD index := by
  calc
    _ = (join (split (word, (0 : BitVec 0)))).1.getMsbD (mainWidth + index) :=
      congrArg (fun state : BitVec (mainWidth + 3) × BitVec 0 =>
        state.1.getMsbD (mainWidth + index)) (join_split (word, (0 : BitVec 0))).symm
    _ = _ := by
      rw [join_high_bit _ index within]
      simp only [split, BitVec.extractLsb'_append_eq_left]

/-- The original prime terminal word supplies the high-counter zero value internally. -/
lemma high_terminalWord (modulus : Nat) : high (TerminalPadding.terminalWord modulus) = 0 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have physical := TerminalPadding.terminalWord_padding_zero modulus (⟨index, within⟩ : Fin 2)
  change (TerminalPadding.terminalWord modulus).getMsbD (modulus.size + index) = false at physical
  rw [high_bit _ index within] at physical
  calc
    _ = false := physical
    _ = _ := (BitVec.getMsbD_zero (w := 2) (i := index)).symm

/-- The terminal word and original zero low register initialize the combined count to zero. -/
lemma terminal_counter_zero (modulus : Nat) :
    (split (TerminalPadding.terminalWord modulus, (0 : BitVec lowWidth))).2 = 0 := by
  change high (TerminalPadding.terminalWord modulus) ++ (0 : BitVec lowWidth) = 0
  rw [high_terminalWord]
  apply BitVec.eq_of_toNat_eq
  change 0 <<< lowWidth ||| 0 = 0
  simp only [Nat.zero_shiftLeft, Nat.zero_or]

/-- The coprime positive input establishes the candidate's initial high bits in the actual word. -/
lemma final_counter_zero (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    (split (PackingBoundary.firstWord (TerminalPadding.finalState modulus input) modulus
      (TerminalPadding.final_admissible modulus input positive bounded)
      (TerminalPadding.final_balance modulus input), (0 : BitVec lowWidth))).2 = 0 := by
  rw [TerminalPadding.final_firstWord modulus input coprime positive bounded]
  exact terminal_counter_zero modulus

/-- Select combined increment only when the unchanged actual divisor-length register is zero. -/
def selectedIncrement {lengthWidth : Nat} (divisorLength : BitVec lengthWidth)
    (state : BitVec (mainWidth + 3) × BitVec lowWidth) :
    BitVec (mainWidth + 3) × BitVec lowWidth :=
  if divisorLength = 0 then increment state else (state.1, state.2 + 1)

/-- Reverse the selected increment using that same retained, unchanged source predicate. -/
def selectedDecrement {lengthWidth : Nat} (divisorLength : BitVec lengthWidth)
    (state : BitVec (mainWidth + 3) × BitVec lowWidth) :
    BitVec (mainWidth + 3) × BitVec lowWidth :=
  if divisorLength = 0 then decrement state else (state.1, state.2 - 1)

/-- The conditional assignments preserve the whole original state on both predicate branches. -/
lemma selectedDecrement_selectedIncrement {lengthWidth : Nat}
    (divisorLength : BitVec lengthWidth) (state : BitVec (mainWidth + 3) × BitVec lowWidth) :
    selectedDecrement divisorLength (selectedIncrement divisorLength state) = state := by
  by_cases terminal : divisorLength = 0
  · simp only [selectedDecrement, selectedIncrement, if_pos terminal, decrement_increment]
  · simp only [selectedDecrement, selectedIncrement, if_neg terminal, BitVec.add_sub_cancel]

/-- The conditional inverse law also holds in the other direction on arbitrary physical data. -/
lemma selectedIncrement_selectedDecrement {lengthWidth : Nat}
    (divisorLength : BitVec lengthWidth) (state : BitVec (mainWidth + 3) × BitVec lowWidth) :
    selectedIncrement divisorLength (selectedDecrement divisorLength state) = state := by
  by_cases terminal : divisorLength = 0
  · simp only [selectedIncrement, selectedDecrement, if_pos terminal, increment_decrement]
  · simp only [selectedIncrement, selectedDecrement, if_neg terminal, BitVec.sub_add_cancel]

/-- Active phases retain every first-word bit, including arbitrary nonzero padding positions. -/
lemma selectedIncrement_active {lengthWidth : Nat} (divisorLength : BitVec lengthWidth)
    (active : divisorLength ≠ 0) (state : BitVec (mainWidth + 3) × BitVec lowWidth) :
    selectedIncrement divisorLength state = (state.1, state.2 + 1) := by
  rw [selectedIncrement, if_neg active]

end QuantumAlg.NumberTheory.SharedEEA.PaddingClock
