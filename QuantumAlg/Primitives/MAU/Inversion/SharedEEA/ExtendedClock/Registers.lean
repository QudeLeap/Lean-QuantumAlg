/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Primitives.MAU.Addition.HRS.IncrementPlacement

/-!
# Actual existing-wire coordinates for the repaired terminal counter

The target consists of precisely the two already identified Work1 tail
positions followed by the original low shift register. The actual HRS
controlled incrementer borrows its required bits from the complete Work2
word and restores them for every incoming value
[HRS16, paper.tex:219-226,232-260]. No new register is allocated.

All remaining Work1 bits, the other three lengths, phase controls, Iter,
and Ctrl remain explicit in the complement. The exact split and inverse
operate on every source frame, including active frames with arbitrary
values at those two Work1 positions. Only later trajectory theorems may
use their proved terminal zero values
[LYL+26, sec_EEA/sub_regshare.tex:16-26,303-315].

This owner supplies concrete coordinate identities for actual gate
placement. It does not replace native arithmetic by an abstract unitary
or assert that the fixed terminal schedule has already been implemented.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ExtendedClockRegisters

noncomputable section

open NumberTheory.SharedEEA

/-- Exactly two existing Work1 bits precede the original finite low counter. -/
def clockWidth (width : Nat) : Nat := 2 + width.size

/-- The full counter reads the proved physical high-bit positions and the actual low shift. -/
def clock {width : Nat} (state : Registers width) : BitVec (clockWidth width) :=
  (PaddingClock.split (state.firstWord, state.shift)).2

/-- The unchanged leading part of the actual borrowed Work2 word. -/
def extra (width : Nat) : Nat := width + 3 - clockWidth width

/-- The original full Work2 always supplies all dirty bits required by the real incrementer. -/
lemma extra_add_clockWidth (width : Nat) : extra width + clockWidth width = width + 3 := by
  have enough : width.size ≤ width := Nat.size_le.mpr Nat.lt_two_pow_self
  unfold extra clockWidth
  omega

/-- Every field outside Work2, the real extended counter, and the existing Phase2 bit. -/
abbrev Remainder (width : Nat) :=
  (BitVec width × BitVec 1) ×
    ((BitVec width.size × BitVec width.size) ×
      (BitVec width.size × ((Bool × Bool) × (Bool × Bool))))

/-- Split and reassemble the exact HRS interface and every complementary physical coordinate. -/
def grouping (width : Nat) : Registers width ≃
    (Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (clockWidth width) × Remainder width)
    where
  toFun state :=
    (((BitVec.equivFin state.secondWord, BitVec.equivFin (clock state)), state.flags.second),
      ((PaddingClock.main state.firstWord, PaddingClock.last state.firstWord),
        ((state.coefficientLength, state.quotientLength),
          (state.divisorLength, ((state.flags.first, state.flags.sign),
            (state.flags.iteration, state.control))))))
  invFun pair :=
    let original := PaddingClock.join (pair.2.1,
      (BitVec.equivFin.symm pair.1.1.2 : BitVec (2 + width.size)))
    { firstWord := original.1
      secondWord := BitVec.equivFin.symm pair.1.1.1
      coefficientLength := pair.2.2.1.1
      quotientLength := pair.2.2.1.2
      divisorLength := pair.2.2.2.1
      shift := original.2
      flags := ⟨pair.2.2.2.2.1.1, pair.1.2, pair.2.2.2.2.1.2, pair.2.2.2.2.2.1⟩
      control := pair.2.2.2.2.2.2 }
  left_inv state := by
    change { state with
      firstWord := (PaddingClock.join (PaddingClock.split (state.firstWord, state.shift))).1
      shift := (PaddingClock.join (PaddingClock.split (state.firstWord, state.shift))).2 } = state
    rw [PaddingClock.join_split]
  right_inv := by
    rintro ⟨⟨⟨work, target⟩, p2⟩,
      ⟨⟨main, last⟩, ⟨⟨lengthT, lengthQ⟩, ⟨lengthR, ⟨⟨p1, sign⟩, ⟨iter, control⟩⟩⟩⟩⟩⟩
    let coordinates : (BitVec width × BitVec 1) × BitVec (2 + width.size) :=
      ((main, last), BitVec.equivFin.symm target)
    change (((work, BitVec.equivFin (PaddingClock.split (PaddingClock.join coordinates)).2), p2),
      ((PaddingClock.split (PaddingClock.join coordinates)).1,
        ((lengthT, lengthQ), (lengthR, ((p1, sign), (iter, control)))))) = _
    rw [PaddingClock.split_join]
    rfl

/-- The complete real target value is unchanged by the exact HRS label encoding. -/
lemma grouping_clock (width : Nat) (state : Registers width) :
    (grouping width state).1.1.2.val = (clock state).toNat := rfl

/-- The borrowed word is precisely Work2, including all unknown state and correlations. -/
lemma grouping_work (width : Nat) (state : Registers width) :
    (grouping width state).1.1.1.val = state.secondWord.toNat := rfl

/-- The existing Phase2 control retains its literal physical source value. -/
lemma grouping_control (width : Nat) (state : Registers width) :
    (grouping width state).1.2 = state.flags.second := rfl

/-- Every actual target bit lies at its stated Work1 high position or original shift position. -/
lemma clock_bit (width : Nat) (index : Fin (clockWidth width)) (state : Registers width) :
    (clock state).getMsbD index.val =
      if index.val < 2 then state.firstWord.getMsbD (width + index.val)
      else state.shift.getMsbD (index.val - 2) := by
  change (PaddingClock.high state.firstWord ++ state.shift).getMsbD index.val = _
  rw [BitVec.getMsbD_append]
  by_cases high : index.val < 2
  · rw [if_neg (by omega), if_pos high]
    exact (PaddingClock.high_bit state.firstWord index.val high).symm
  · rw [if_pos (by omega), if_neg high]

/-- Native HRS physical order: the clock, full borrowed Work2, and Phase2. -/
def physicalIndex (width index : Nat) : Nat :=
  if index < clockWidth width then
    if index < 2 then width + index
    else 2 * (width + 3) + 3 * width.size + (index - 2)
  else if index < clockWidth width + width + 3 then
    width + 3 + (index - clockWidth width)
  else 2 * (width + 3) + 4 * width.size + 1

/-- Every borrowed bit is an actual Work2 wire. -/
lemma physicalIndex_work (width : Nat) (index : Fin (width + 3)) :
    physicalIndex width (clockWidth width + index.val) =
      (secondWordBit width index).wire.val := by
  rw [secondWordBit_wire]
  have afterClock : ¬clockWidth width + index.val < clockWidth width := by omega
  have beforeControl : clockWidth width + index.val < clockWidth width + width + 3 := by
    have bound := index.isLt
    omega
  simp only [physicalIndex, if_neg afterClock, if_pos beforeControl,
    Nat.add_sub_cancel_left]

/-- Both high-counter addresses are exactly the pre-existing Work1 tail positions. -/
lemma physicalIndex_high (width : Nat) (index : Fin 2) :
    physicalIndex width index.val =
      (firstWordBit width ⟨width + index.val, by have bound := index.isLt; omega⟩).wire.val := by
  rw [firstWordBit_wire]
  have bound := index.isLt
  have inClock : index.val < clockWidth width := by unfold clockWidth; omega
  simp only [physicalIndex, if_pos inClock, if_pos bound]

/-- Every low-counter address is the unchanged actual shift-register wire. -/
lemma physicalIndex_low (width : Nat) (index : Fin width.size) :
    physicalIndex width (2 + index.val) = (shiftBit width index).wire.val := by
  rw [shiftBit_wire]
  have bound := index.isLt
  have inClock : 2 + index.val < clockWidth width := by unfold clockWidth; omega
  have afterHigh : ¬2 + index.val < 2 := by omega
  simp only [physicalIndex, if_pos inClock, if_neg afterHigh, Nat.add_sub_cancel_left]

/-- The incrementer control is the original Phase2 physical wire. -/
lemma physicalIndex_control (width : Nat) :
    physicalIndex width (clockWidth width + width + 3) =
      (phase2Bit width).wire.val := by
  rw [phase2Bit_wire]
  have afterClock : ¬clockWidth width + width + 3 < clockWidth width := by omega
  simp only [physicalIndex, if_neg afterClock, Nat.lt_irrefl, if_false]

end

end QuantumAlg.MAU.Inversion.SharedEEA.ExtendedClockRegisters
