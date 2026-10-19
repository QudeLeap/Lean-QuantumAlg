/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Division.Advance

/-!
# Actual phase-two pre-shift and a complete native division microstep

The optimized native source really executes one left rotation/increment
followed by two right rotations/decrements in phase two
[LYL+26, sec_EEA/sub_opt.tex:37-40]. Their composition is proved below on
the complete existing register state, including finite intermediate wrap.
It sends the actual entry rotation and counter to the previously verified
remainder arithmetic frame [LYL+26, sec_EEA/sub_regshare.tex:279-287].

The concluding equation applies `NativeMicrostep.step` itself, hence the
already certified single native program. It includes all eight source
blocks, rather than assuming that an arithmetic-entry frame was supplied
by a caller. Entry frames are mathematical basis specifications; the
first-phase trajectory and repaired terminal dispatch remain separate.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.DivisionEntry

noncomputable section

open RemainderPhaseFrame NumberTheory.SharedEEA

private lemma cast_rotateRight {left right : Nat} (equal : left = right)
    (word : BitVec left) (shift : Nat) :
    (word.cast equal).rotateRight shift = (word.rotateRight shift).cast equal := by
  cases equal
  rfl

private lemma original_shift_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    (Alignment.align state.remainder state.divisor).places - count < 2 ^ modulus.size.size :=
  ((Nat.sub_le (Alignment.align state.remainder state.divisor).places count).trans
    (RemainderPhaseFrame.alignment_le state modulus valid conserved)).trans_lt
      (Nat.lt_size_self modulus.size)

/-- Complete physical frame before this phase-two native microstep executes its pre-shift. -/
def entryFrame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) : Registers modulus.size :=
  { frame state modulus count valid conserved active beforeEnd iteration with
    secondWord := (WordRotation.packRotatedWork2
      ((Alignment.align state.remainder state.divisor).places - count)
        (DivisionCapacity.work2Payload state modulus valid conserved)).cast
          (DivisionCapacity.work2_width state modulus valid conserved)
    shift := BitVec.ofNatLT ((Alignment.align state.remainder state.divisor).places - count)
      (original_shift_fits state modulus count valid conserved) }

/-- The real increment and two decrements compose exactly, including intermediate finite wrap. -/
lemma native_descending (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = false)
    (second : state.flags.second = true) (positive : 0 < state.shift.toNat) :
    GuardedShift.step false state =
      { state with secondWord := state.secondWord.rotateRight 1, shift := state.shift - 1 } := by
  rw [GuardedShift.step_eq_source width false state clean, GuardedShift.sourceStep,
    first, if_pos rfl, second]
  change GuardedShift.descending (GuardedShift.ascending state) = _
  rw [GuardedShift.descending_ascending_eq_low state positive,
    WordRotation.rotateRight_rotateLeft]

private lemma word_after (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    ((entryFrame state modulus count valid conserved active beforeEnd iteration).secondWord
      |>.rotateRight 1) =
        (frame state modulus count valid conserved active beforeEnd iteration).secondWord := by
  have countEq : (Alignment.align state.remainder state.divisor).places - count =
      DivisionWindow.shift state count + 1 := by
    unfold DivisionWindow.shift
    omega
  change ((WordRotation.packRotatedWork2
    ((Alignment.align state.remainder state.divisor).places - count)
      (DivisionCapacity.work2Payload state modulus valid conserved)).cast
        (DivisionCapacity.work2_width state modulus valid conserved)).rotateRight 1 = _
  rw [cast_rotateRight, countEq, WordRotation.packRotatedWork2_unshift]
  rfl

private lemma shift_after (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (entryFrame state modulus count valid conserved active beforeEnd iteration).shift - 1 =
      (frame state modulus count valid conserved active beforeEnd iteration).shift := by
  have countEq : (Alignment.align state.remainder state.divisor).places - count =
      DivisionWindow.shift state count + 1 := by
    unfold DivisionWindow.shift
    omega
  have within := original_shift_fits state modulus count valid conserved
  have oneFits : 1 < 2 ^ modulus.size.size := by omega
  rw [BitVec.sub_eq_iff_eq_add]
  apply BitVec.eq_of_toNat_eq
  change (Alignment.align state.remainder state.divisor).places - count =
    ((frame state modulus count valid conserved active beforeEnd iteration).shift + 1).toNat
  rw [BitVec.toNat_add]
  change (Alignment.align state.remainder state.divisor).places - count =
    (DivisionWindow.shift state count + 1 % 2 ^ modulus.size.size) % 2 ^ modulus.size.size
  rw [Nat.mod_eq_of_lt oneFits, ← countEq, Nat.mod_eq_of_lt within]

/-- The executed pre-shift reaches the exact complete arithmetic frame of the division proof. -/
lemma native_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    GuardedShift.step false
      (entryFrame state modulus count valid conserved active beforeEnd iteration) =
        frame state modulus count valid conserved active beforeEnd iteration := by
  have positive : 0 < (entryFrame state modulus count valid conserved active
      beforeEnd iteration).shift.toNat := by
    change 0 < (Alignment.align state.remainder state.divisor).places - count
    omega
  rw [native_descending modulus.size _ rfl rfl rfl positive,
    word_after state modulus count valid conserved active beforeEnd iteration,
    shift_after state modulus count valid conserved active beforeEnd iteration]
  rfl

/-- One entire certified native microstep advances the complete reachable division frame. -/
lemma microstep_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    let expected := DivisionAdvance.nextFrame state modulus count
      valid conserved active beforeEnd iteration
    NativeMicrostep.step modulus.size
      (entryFrame state modulus count valid conserved active beforeEnd iteration) =
      { expected with flags :=
        ⟨decide (expected.shift = (0#modulus.size.size)),
          !decide (expected.shift = (0#modulus.size.size)), false, iteration⟩ } := by
  dsimp only
  rw [NativeMicrostep.step, native_frame state modulus count
    valid conserved active beforeEnd iteration]
  exact DivisionAdvance.native_tail_frame state modulus count
    valid conserved active beforeEnd iteration

end

end QuantumAlg.MAU.Inversion.SharedEEA.DivisionEntry
