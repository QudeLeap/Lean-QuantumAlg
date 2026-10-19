/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Primitives.MAU.Addition.HRS.IncrementPlacement

/-!
# Actual source coordinates for the low shift-counter incrementer

The original shift field has `Nat.size n` bits, and both shared words have
`n+3` bits [LYL+26, sec_EEA/sub_regshare.tex:16-26]. The HRS incrementer can
borrow that many least-significant bits of the existing Work1 word and
restore them exactly, with arbitrary incoming values
[HRS16, paper.tex:219-224]. Its control is the existing Phase2 bit.

This owner gives the exact field grouping, its inverse, and every physical
address for that native interface. The three other lengths, Work2, other
flags, and Ctrl are explicitly retained. The later placement owner must
transport the actual elementary HRS circuit through these coordinates;
the mathematical record update here is not a declaration of a new gate.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.LowShiftRegisters

noncomputable section

/-- The part of Work1 above the internally borrowed low counter-width bits. -/
def extra (width : Nat) : Nat := width + 3 - width.size

/-- Every source width supplies the needed borrowed bits internally, including width zero. -/
lemma extra_add_length (width : Nat) : extra width + width.size = width + 3 := by
  have enough : width.size ≤ width := Nat.size_le.mpr Nat.lt_two_pow_self
  dsimp only [extra]
  omega

/-- Every original field outside Work1, low shift, and Phase2. -/
abbrev Remainder (width : Nat) :=
  BitVec (width + 3) ×
    ((BitVec width.size × BitVec width.size) ×
      (BitVec width.size × ((Bool × Bool) × (Bool × Bool))))

/-- Group the exact native HRS interface with its full physical complement. -/
def grouping (width : Nat) :
    Registers width ≃
      (Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) width.size × Remainder width) where
  toFun state :=
    (((BitVec.equivFin state.firstWord, BitVec.equivFin state.shift), state.flags.second),
      (state.secondWord, ((state.coefficientLength, state.quotientLength),
        (state.divisorLength, ((state.flags.first, state.flags.sign),
          (state.flags.iteration, state.control))))))
  invFun pair :=
    { firstWord := BitVec.equivFin.symm pair.1.1.1
      secondWord := pair.2.1
      coefficientLength := pair.2.2.1.1
      quotientLength := pair.2.2.1.2
      divisorLength := pair.2.2.2.1
      shift := BitVec.equivFin.symm pair.1.1.2
      flags := ⟨pair.2.2.2.2.1.1, pair.1.2, pair.2.2.2.2.1.2, pair.2.2.2.2.2.1⟩
      control := pair.2.2.2.2.2.2 }
  left_inv := by
    rintro ⟨word1, word2, lengthT, lengthQ, lengthR, shift, ⟨p1, p2, sign, iter⟩, control⟩
    rfl
  right_inv := by
    rintro ⟨⟨⟨word1, shift⟩, p2⟩,
      ⟨word2, ⟨⟨lengthT, lengthQ⟩, ⟨lengthR, ⟨⟨p1, sign⟩, ⟨iter, control⟩⟩⟩⟩⟩⟩
    rfl

/-- The selected target is exactly the original low shift, without any widened-counter cast. -/
lemma grouping_shift (width : Nat) (state : Registers width) :
    (grouping width state).1.1.2.val = state.shift.toNat := rfl

/-- The borrowed interface is exactly the complete original Work1 word. -/
lemma grouping_work (width : Nat) (state : Registers width) :
    (grouping width state).1.1.1.val = state.firstWord.toNat := rfl

/-- Every bit of the arithmetic target is the same actual little-endian low-shift bit. -/
lemma grouping_shift_bit (width : Nat) (index : Fin width.size) (state : Registers width) :
    (Addition.HRS.bridgeHighBit (width + 3) width.size index).get (grouping width state).1 =
      (shiftBit width index.rev).get state := by
  rw [Addition.HRS.hrsBridgeHighBit_get, shiftBit_get, grouping_shift]
  have reverse : width.size - 1 - index.rev.val = index.val := by
    rw [Fin.val_rev]
    have bound := index.isLt
    omega
  simp only [BitVec.getMsbD_eq_getLsbD, index.rev.isLt, decide_true,
    Bool.true_and, reverse, BitVec.getLsbD]

/-- Every borrowed-word bit is its actual Work1 position, including unknown padding bits. -/
lemma grouping_work_bit (width : Nat) (index : Fin (width + 3)) (state : Registers width) :
    (Addition.HRS.bridgeLowBit (width + 3) width.size index).get (grouping width state).1 =
      (firstWordBit width index.rev).get state := by
  rw [Addition.HRS.hrsBridgeLowBit_get, firstWordBit_get, grouping_work]
  have reverse : width + 3 - 1 - index.rev.val = index.val := by
    rw [Fin.val_rev]
    have bound := index.isLt
    omega
  simp only [BitVec.getMsbD_eq_getLsbD, index.rev.isLt, decide_true,
    Bool.true_and, reverse, BitVec.getLsbD]

/-- The incrementer's preserved control is the actual Phase2 field. -/
lemma grouping_control (width : Nat) (state : Registers width) :
    (Addition.HRS.bridgeDirtyBit (width + 3) width.size).get (grouping width state).1 =
      (phase2Bit width).get state := rfl

/-- Map the native Work1/shift/control addresses onto their actual source wires. -/
def physicalIndex (width index : Nat) : Nat :=
  if index < width.size then 2 * (width + 3) + 3 * width.size + index
  else if index < width.size + (width + 3) then index - width.size
  else 2 * (width + 3) + 4 * width.size + 1

lemma physicalIndex_work (width : Nat) (index : Fin (width + 3)) :
    physicalIndex width (width.size + index.val) = (firstWordBit width index).wire.val := by
  rw [firstWordBit_wire]
  have lower : ¬width.size + index.val < width.size := by omega
  have upper : width.size + index.val < width.size + (width + 3) := by
    have bound := index.isLt
    omega
  simp only [physicalIndex, if_neg lower, if_pos upper, Nat.add_sub_cancel_left]

lemma physicalIndex_shift (width : Nat) (index : Fin width.size) :
    physicalIndex width index.val = (shiftBit width index).wire.val := by
  rw [shiftBit_wire]
  simp only [physicalIndex, if_pos index.isLt]

lemma physicalIndex_control (width : Nat) :
    physicalIndex width (width.size + (width + 3)) = (phase2Bit width).wire.val := by
  rw [phase2Bit_wire]
  have lower : ¬width.size + (width + 3) < width.size := by omega
  simp only [physicalIndex, if_neg lower, Nat.lt_irrefl, if_false]

/-- Every native incrementer wire already lies inside the original complete source frame. -/
lemma physicalIndex_within (width : Nat) (index : Fin (width + 3 + width.size + 1)) :
    physicalIndex width index.val < (encoding width).width := by
  rw [encoding_width]
  unfold physicalIndex
  split
  · omega
  · split
    · omega
    · omega

/-- No actual incrementer control, target, or borrowed word position is aliased. -/
lemma physicalIndex_injective (width : Nat) :
    Function.Injective
      (fun index : Fin (width + 3 + width.size + 1) => physicalIndex width index.val) := by
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

end

end QuantumAlg.MAU.Inversion.SharedEEA.LowShiftRegisters
