/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison

/-!
# Exact shared-register coordinates for the retained input fold

The source's fold writes Iter and conditionally complements the divisor
[LYL+26, sec_EEA/sub_4phase.tex:108-117]. Its arithmetic can use the existing
complete Work2 word: the three initial zero padding bits do not change the
represented divisor. The comparison's arbitrary helper is the existing Ctrl.
The comparison algorithm and helper restoration are from the actual Gidney
construction [G17, paper.tex:380-389].

This owner groups those actual fields and their complement explicitly.
The grouping and its inverse retain every Work1, length, and other flag bit.
It supplies the semantic and physical coordinates for later tensor placement;
it neither allocates another register nor declares an arithmetic gate.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.FoldRegisters

noncomputable section

/-- Every coordinate outside the actual comparison word, Iter, and Ctrl. -/
abbrev Remainder (width : Nat) :=
  BitVec (width + 3) ×
    (((BitVec width.size × BitVec width.size) × (BitVec width.size × BitVec width.size)) ×
      ((Bool × Bool) × Bool))

/-- Extract and reassemble all named fields, preserving the word's exact unsigned value. -/
def grouping (width : Nat) :
    Registers width ≃ (Addition.Gidney.Registers (width + 3) × Remainder width) where
  toFun state :=
    ((state.flags.iteration, (BitVec.equivFin state.secondWord, state.control)),
      (state.firstWord, (((state.coefficientLength, state.quotientLength),
        (state.divisorLength, state.shift)), ((state.flags.first, state.flags.second),
          state.flags.sign))))
  invFun pair :=
    { firstWord := pair.2.1
      secondWord := BitVec.equivFin.symm pair.1.2.1
      coefficientLength := pair.2.2.1.1.1
      quotientLength := pair.2.2.1.1.2
      divisorLength := pair.2.2.1.2.1
      shift := pair.2.2.1.2.2
      flags := ⟨pair.2.2.2.1.1, pair.2.2.2.1.2, pair.2.2.2.2, pair.1.1⟩
      control := pair.1.2.2 }
  left_inv := by
    rintro ⟨word1, word2, lengthT, lengthQ, lengthR, shift, ⟨p1, p2, sign, iter⟩, control⟩
    rfl
  right_inv := by
    rintro ⟨⟨iter, word2, control⟩,
      ⟨word1, ⟨⟨⟨lengthT, lengthQ⟩, ⟨lengthR, shift⟩⟩, ⟨⟨p1, p2⟩, sign⟩⟩⟩⟩
    rfl

/-- The focused arithmetic word is exactly the full Work2 value, including its actual padding. -/
theorem grouping_word (width : Nat) (state : Registers width) :
    ((grouping width state).1.2.1).val = state.secondWord.toNat := rfl

/-- The actual comparison flag is Iter, which retains the source complement history. -/
theorem grouping_flag (width : Nat) (state : Registers width) :
    (Addition.Gidney.flagBit (width + 3)).get (grouping width state).1 =
      (iterationBit width).get state := rfl

/-- The arithmetic helper is the already present Ctrl bit, with no cleanliness condition. -/
theorem grouping_helper (width : Nat) (state : Registers width) :
    (Addition.Gidney.helperBit (width + 3)).get (grouping width state).1 =
      (controlBit width).get state := rfl

/-- Every focused little-endian word bit agrees with the same actual Work2 physical bit. -/
theorem grouping_word_bit (width : Nat) (index : Fin (width + 3)) (state : Registers width) :
    (Addition.Gidney.wordBit (width + 3) index).get (grouping width state).1 =
      (secondWordBit width index.rev).get state := by
  rw [Addition.Gidney.gidneyWordBit_get, secondWordBit_get, grouping_word]
  have reverse : width + 3 - 1 - index.rev.val = index.val := by
    rw [Fin.val_rev]
    have bound := index.isLt
    omega
  simp only [BitVec.getMsbD_eq_getLsbD, index.rev.isLt, decide_true,
    Bool.true_and, reverse, BitVec.getLsbD]

/-- The native comparison wire order mapped to existing canonical source physical identities. -/
def physicalIndex (width index : Nat) : Nat :=
  if index = 0 then 2 * (width + 3) + 4 * width.size + 3
  else if index < width + 4 then width + 3 + (index - 1)
  else 2 * (width + 3) + 4 * width.size + 4

theorem physicalIndex_flag (width : Nat) :
    physicalIndex width 0 = (iterationBit width).wire.val := by
  rw [iterationBit_wire]
  simp [physicalIndex]

theorem physicalIndex_word (width : Nat) (index : Fin (width + 3)) :
    physicalIndex width (1 + index.val) = (secondWordBit width index).wire.val := by
  rw [secondWordBit_wire]
  have bound := index.isLt
  have nonzero : 1 + index.val ≠ 0 := by omega
  have inside : 1 + index.val < width + 4 := by omega
  simp only [physicalIndex, if_neg nonzero, if_pos inside, Nat.add_sub_cancel_left]

theorem physicalIndex_helper (width : Nat) :
    physicalIndex width (width + 4) = (controlBit width).wire.val := by
  rw [controlBit_wire]
  simp [physicalIndex]

/-- Every physical comparison address lies in the existing full source frame. -/
theorem physicalIndex_within (width : Nat) (index : Fin (width + 5)) :
    physicalIndex width index.val < (encoding width).width := by
  rw [encoding_width]
  unfold physicalIndex
  split
  · omega
  · split
    · have bound := index.isLt
      omega
    · omega

/-- The focused native program never aliases its flag, helper, or any word bit. -/
theorem physicalIndex_injective (width : Nat) :
    Function.Injective (fun index : Fin (width + 5) => physicalIndex width index.val) := by
  intro left right same
  apply Fin.ext
  have leftBound := left.isLt
  have rightBound := right.isLt
  change physicalIndex width left.val = physicalIndex width right.val at same
  unfold physicalIndex at same
  split at same <;> split at same
  all_goals try split at same
  all_goals try split at same
  all_goals omega

/-- The comparison's full source-state specification under this explicit field grouping. -/
def comparisonStep (width pivot : Nat) (state : Registers width) : Registers width :=
  (grouping width).symm
    (Addition.Gidney.comparisonOutput pivot (grouping width state).1, (grouping width state).2)

/-- The transported comparison changes only Iter by the actual full-word inequality. -/
theorem comparisonStep_eq (width pivot : Nat) (state : Registers width) :
    comparisonStep width pivot state =
      { state with flags := { state.flags with
          iteration := state.flags.iteration ^^ decide (state.secondWord.toNat < pivot) } } := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift, ⟨p1, p2, sign, iter⟩,
    control⟩
  rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.FoldRegisters
