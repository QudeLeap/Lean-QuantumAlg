/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ExtendedClock.Registers
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Terminal.Predicate
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Boundary.Predicate

/-!
# Exact original-frame positions of the rotating terminal tail

The source retains its forward history while Work2 continues to rotate
[LYL+26, sec_EEA/sub_opt.tex:37-40,74-84;
LYL+26, sec_EEA/sub_4phase.tex:105,121-128]. This mathematical frame places
the complete displacement in the two original Work1 positions and the
original low counter. Every other field, including Iter, is retained.

The exact complete-clock equations and actual predicate values below do
not define another transition engine. They specify positions for the
single native loop's terminal refinement. The independent schedule must
supply the proved no-wrap bound; no low-counter nonzero assumption is
made, so positive positions after a low wrap are included.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.TerminalPosition

noncomputable section

open NumberTheory.SharedEEA ExtendedClockRegisters

/-- Reassemble the actual two reused positions and low field around all unchanged Work1 bits. -/
def pair {width : Nat} (initial : Registers width) (count : Nat) :
    BitVec (width + 3) × BitVec width.size :=
  PaddingClock.join ((PaddingClock.main initial.firstWord, PaddingClock.last initial.firstWord),
    BitVec.ofNat (2 + width.size) count)

/-- Full physical position includes rotated Work2, complete clock, and unchanged history. -/
def frame {width : Nat} (initial : Registers width) (count : Nat) : Registers width :=
  { initial with
    firstWord := (pair initial count).1
    secondWord := initial.secondWord.rotateLeft count
    shift := (pair initial count).2 }

/-- The actual split reads the entire finite count and precisely the original complement. -/
lemma pair_split {width : Nat} (initial : Registers width) (count : Nat) :
    PaddingClock.split (pair initial count) =
      ((PaddingClock.main initial.firstWord, PaddingClock.last initial.firstWord),
        BitVec.ofNat (2 + width.size) count) :=
  PaddingClock.split_join _

/-- The actual full clock contains all displacement bits, even when its low field is zero. -/
lemma frame_clock {width : Nat} (initial : Registers width) (count : Nat) :
    clock (frame initial count) = BitVec.ofNat (2 + width.size) count :=
  congrArg Prod.snd (pair_split initial count)

/-- Before complete wrap, the actual physical clock's natural value is exactly the displacement. -/
lemma frame_clock_value {width : Nat} (initial : Registers width) (count : Nat)
    (within : count < 2 ^ (2 + width.size)) :
    (clock (frame initial count)).toNat = count := by
  rw [frame_clock]
  exact Nat.mod_eq_of_lt within

/-- The physical main Work1 and final bit are unchanged, rather than merely equal in dimension. -/
lemma frame_untouched {width : Nat} (initial : Registers width) (count : Nat) :
    PaddingClock.main (frame initial count).firstWord = PaddingClock.main initial.firstWord ∧
      PaddingClock.last (frame initial count).firstWord = PaddingClock.last initial.firstWord := by
  have actual := congrArg Prod.fst (pair_split initial count)
  exact ⟨congrArg Prod.fst actual, congrArg Prod.snd actual⟩

/-- Every original finite length, control, and history coordinate is fixed in the position. -/
lemma frame_retained {width : Nat} (initial : Registers width) (count : Nat) :
    (frame initial count).coefficientLength = initial.coefficientLength ∧
      (frame initial count).quotientLength = initial.quotientLength ∧
      (frame initial count).divisorLength = initial.divisorLength ∧
      (frame initial count).flags = initial.flags ∧
      (frame initial count).control = initial.control :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The original terminal zero clock makes the zero position exactly the complete initial frame. -/
lemma frame_zero {width : Nat} (initial : Registers width) (zero : clock initial = 0) :
    frame initial 0 = initial := by
  have coordinates :
      ((PaddingClock.main initial.firstWord, PaddingClock.last initial.firstWord),
        BitVec.ofNat (2 + width.size) 0) =
          PaddingClock.split (initial.firstWord, initial.shift) := by
    exact congrArg
      (fun value : BitVec (2 + width.size) =>
        ((PaddingClock.main initial.firstWord, PaddingClock.last initial.firstWord), value))
      ((TerminalTail.literal_zero (2 + width.size)).trans zero.symm)
  have same : pair initial 0 = (initial.firstWord, initial.shift) :=
    (congrArg PaddingClock.join coordinates).trans (PaddingClock.join_split _)
  unfold frame
  rw [same, TerminalTail.rotateLeft_zero]

/-- One actual combined increment advances precisely these physical coordinates. -/
lemma pair_increment {width : Nat} (initial : Registers width) (count : Nat) :
    PaddingClock.increment (pair initial count) = pair initial (count + 1) := by
  unfold PaddingClock.increment
  rw [pair_split, TerminalTail.increment_ofNat]
  rfl

/-- The complete physical clock cannot vanish at a positive position before its first wrap. -/
lemma frame_clock_nonzero {width : Nat} (initial : Registers width) (count : Nat)
    (positive : 0 < count) (within : count < 2 ^ (2 + width.size)) :
    clock (frame initial count) ≠ 0 := by
  rw [frame_clock]
  exact TerminalTail.ofNat_nonzero count positive within

private lemma clock_zero_of_fields {width : Nat} (state : Registers width)
    (low : state.shift = 0) (high : PaddingClock.high state.firstWord = 0) : clock state = 0 := by
  change PaddingClock.high state.firstWord ++ state.shift = 0
  rw [high, low]
  apply BitVec.eq_of_toNat_eq
  change 0 <<< width.size ||| 0 = 0
  simp only [Nat.zero_shiftLeft, Nat.zero_or]

/-- The actual new phase-zero predicate is false at every positive complete-clock position. -/
lemma phase_condition_false {width : Nat} (initial : Registers width) (count : Nat)
    (finished : initial.divisorLength = 0)
    (positive : 0 < count) (within : count < 2 ^ (2 + width.size)) :
    TerminalPredicate.condition (frame initial count) = false := by
  rw [TerminalPredicate.condition_terminal _ (show (frame initial count).divisorLength = 0 from
    finished)]
  apply decide_eq_false
  rintro ⟨low, high⟩
  exact frame_clock_nonzero initial count positive within
    (clock_zero_of_fields (frame initial count) low high)

/-- The actual boundary also stays false, without requiring a nonzero low counter. -/
lemma boundary_condition_false {width : Nat} (initial : Registers width) (count : Nat)
    (finished : initial.divisorLength = 0)
    (positive : 0 < count) (within : count < 2 ^ (2 + width.size)) :
    BoundaryPredicate.condition (frame initial count) = false := by
  rw [BoundaryPredicate.condition_terminal _ (show (frame initial count).divisorLength = 0 from
    finished)]
  apply decide_eq_false
  rintro ⟨_, low, high⟩
  exact frame_clock_nonzero initial count positive within
    (clock_zero_of_fields (frame initial count) low high)

/-- Actual right rotation by the retained complete count recovers every Work2 bit. -/
lemma decode_word {width : Nat} (initial : Registers width) (count : Nat)
    (within : count < 2 ^ (2 + width.size)) :
    (frame initial count).secondWord.rotateRight (clock (frame initial count)).toNat =
      initial.secondWord := by
  rw [frame_clock_value initial count within]
  exact WordRotation.rotateRight_rotateLeft initial.secondWord count

end

end QuantumAlg.MAU.Inversion.SharedEEA.TerminalPosition
