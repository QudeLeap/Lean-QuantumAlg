/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Alignment.PhaseFrame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Alignment.Prelude

/-!
# Complete actual alignment microstep from the retained shift

The same native eight-block program first rotates the complete old Work2
and increments its finite shift. It then compares the whole remainder to
the actually shifted divisor and writes the result into Phase2 through
the real ordered control update [LYL+26, sec_EEA/sub_opt.tex:37-79].

The output contains both unchanged complete payloads at the new rotation,
the exact new shift, and Sign zero. Original macro capacity discharges all
physical-window and finite-counter bounds. The quotient-size bound only
describes active positions; the actual instruction starts from its old
shift and performs the explicit gate increment, not a precomputed count.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.AlignmentAdvance

noncomputable section

open NumberTheory.SharedEEA AlignmentPhaseFrame

private theorem word_after (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    (frame state modulus count valid conserved beforeEnd.le false iteration).secondWord.rotateLeft
        1 =
      (frame state modulus (count + 1) valid conserved (by omega) false iteration).secondWord := by
  change ((WordRotation.packRotatedWork2 count
    (DivisionCapacity.work2Payload state modulus valid conserved)).cast
      (DivisionCapacity.work2_width state modulus valid conserved)).rotateLeft 1 = _
  rw [CoefficientPhaseAction.rotate_cast, WordRotation.packRotatedWork2_shift]
  rfl

private theorem shift_after (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    (frame state modulus count valid conserved beforeEnd.le false iteration).shift + 1 =
      (frame state modulus (count + 1) valid conserved (by omega) false iteration).shift := by
  have bounded := AlignmentPhaseFrame.shift_fits state modulus (count + 1)
    valid conserved (by omega)
  have oneFits : 1 < 2 ^ modulus.size.size := by omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add]
  change (count + 1 % 2 ^ modulus.size.size) % 2 ^ modulus.size.size = count + 1
  rw [Nat.mod_eq_of_lt oneFits, Nat.mod_eq_of_lt bounded]

/-- The real left-shift gates advance the entire original frame, with exact finite shift value. -/
theorem pre_shift_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    GuardedShift.step false
      (frame state modulus count valid conserved beforeEnd.le false iteration) =
      frame state modulus (count + 1) valid conserved (by omega) false iteration := by
  have within :
      (frame state modulus count valid conserved beforeEnd.le false iteration).shift.toNat + 1 <
        2 ^ modulus.size.size :=
    AlignmentPhaseFrame.shift_fits state modulus (count + 1) valid conserved (by omega)
  rw [AlignmentPrelude.pre_shift modulus.size _ rfl rfl rfl within,
    word_after state modulus count valid conserved beforeEnd iteration,
    shift_after state modulus count valid conserved beforeEnd iteration]
  rfl

/-- One complete native microstep records its actual comparison in Phase2 and clears Sign. -/
theorem microstep_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    NativeMicrostep.step modulus.size
      (frame state modulus count valid conserved beforeEnd.le false iteration) =
      { frame state modulus (count + 1) valid conserved (by omega) false iteration with
        flags := ⟨false, decide (state.remainder < state.divisor * 2 ^ (count + 1)),
          false, iteration⟩ } := by
  let after := frame state modulus (count + 1) valid conserved (by omega)
    (decide (state.remainder < state.divisor * 2 ^ (count + 1))) iteration
  have divisor : after.divisorLength ≠ (0#modulus.size.size) := by
    intro zero
    have value := congrArg (fun word : BitVec modulus.size.size => word.toNat) zero
    change state.divisor.size = 0 at value
    have positive := Nat.size_pos.mpr active
    omega
  have shift : after.shift ≠ (0#modulus.size.size) := by
    intro zero
    have value := congrArg (fun word : BitVec modulus.size.size => word.toNat) zero
    change count + 1 = 0 at value
    omega
  rw [NativeMicrostep.step,
    pre_shift_frame state modulus count valid conserved beforeEnd iteration,
    AlignmentPhaseFrame.native_frame state modulus (count + 1)
      valid conserved active (by omega) iteration]
  exact AlignmentPrelude.tail_frame modulus.size after rfl rfl rfl rfl divisor shift

end

end QuantumAlg.MAU.Inversion.SharedEEA.AlignmentAdvance
