/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Consume.Action
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Retained
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Tail

/-!
# Complete native coefficient arithmetic and post-shift advancement

After the actual quotient exchange, the existing native coefficient block
updates the aligned integer window and retains its possibly nonzero
fraction. Its actual post-shift rotates the complete updated Work2 and
increments the live finite counter
[LYL+26, sec_EEA/sub_regshare.tex:263-264,288-296]. Every original Work1 bit,
remaining length, and Iter is preserved, while signed arithmetic clears
Sign before the ordered control suffix.

The basis frame below is the complete output specification of those actual
programs. It neither prepares input-dependent data nor changes the original
admissible macro domain. No future terminal-padding assertion is inferred
from this active coefficient-phase step.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.CoefficientAdvance

noncomputable section

open NumberTheory.SharedEEA CoefficientPhaseFrame

private theorem next_shift_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (beforeEnd : count < state.quotient.size) : count + 1 < 2 ^ modulus.size.size :=
  (show count + 1 ≤ modulus.size by
    have bound := CoefficientPhaseFrame.quotient_size_le state modulus valid conserved
    omega).trans_lt (Nat.lt_size_self modulus.size)

/-- Complete basis frame after the real coefficient arithmetic and its actual one-bit rotation. -/
def nextFrame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    Registers modulus.size :=
  { frame state modulus count valid conserved active beforeEnd iteration with
    secondWord := (PackedCoefficientWindow.word state modulus (count + 1)
      valid conserved active).cast (CoefficientCapacity.work2_width state modulus valid conserved)
    shift := BitVec.ofNatLT (count + 1)
      (next_shift_fits state modulus count valid conserved beforeEnd)
    flags := ⟨true, false, false, iteration⟩ }

/-- Real signed arithmetic and the actual post-shift produce the entire next coefficient frame. -/
theorem native_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    GuardedShift.step true (ArithmeticBlocks.coefficientStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration)) =
        nextFrame state modulus count valid conserved active beforeEnd iteration := by
  let original := frame state modulus count valid conserved active beforeEnd iteration
  let after := ArithmeticBlocks.coefficientStep modulus.size original
  let expected := nextFrame state modulus count valid conserved active beforeEnd iteration
  let selected := window state modulus valid conserved
  have retained := congrArg
    (fun value : ArithmeticWindowRegisters.Complement selected => value.2.2)
    (CoefficientPhaseAction.native_complement state modulus count
      valid conserved active beforeEnd iteration)
  have first : after.flags.first = true := congrArg
    (fun value : ArithmeticWindowPreservation.Retained modulus.size => value.2.2.1.1) retained
  have second : after.flags.second = false := congrArg
    (fun value : ArithmeticWindowPreservation.Retained modulus.size => value.2.2.1.2) retained
  have clean : after.control = false :=
    ArithmeticBlocks.coefficientStep_control modulus.size original
  have shiftRetained : after.shift = original.shift := congrArg
    (fun value : ArithmeticWindowPreservation.Retained modulus.size => value.2.1.2) retained
  have within : after.shift.toNat + 1 < 2 ^ modulus.size.size := by
    rw [shiftRetained]
    exact next_shift_fits state modulus count valid conserved beforeEnd
  rw [CoefficientRetained.post_shift_ascending modulus.size after clean first second within]
  apply Registers.ext_fields
    { after with secondWord := after.secondWord.rotateLeft 1, shift := after.shift + 1 } expected
  · exact CoefficientRetained.native_firstWord modulus.size original rfl rfl rfl
      (window_fits state modulus valid conserved)
  · exact CoefficientPhaseAction.native_word_then_rotation state modulus count
      valid conserved active beforeEnd iteration
  · exact congrArg
      (fun value : ArithmeticWindowPreservation.Retained modulus.size => value.1.1) retained
  · exact congrArg
      (fun value : ArithmeticWindowPreservation.Retained modulus.size => value.1.2) retained
  · exact congrArg
      (fun value : ArithmeticWindowPreservation.Retained modulus.size => value.2.1.1) retained
  · have shiftSame : after.shift = original.shift := congrArg
      (fun value : ArithmeticWindowPreservation.Retained modulus.size => value.2.1.2) retained
    change after.shift + 1 = expected.shift
    rw [shiftSame]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add]
    change (count + 1 % 2 ^ modulus.size.size) % 2 ^ modulus.size.size = count + 1
    have bound := next_shift_fits state modulus count valid conserved beforeEnd
    have oneFits : 1 < 2 ^ modulus.size.size := by omega
    rw [Nat.mod_eq_of_lt oneFits, Nat.mod_eq_of_lt bound]
  · exact first
  · exact second
  · exact CoefficientPhaseFrame.native_sign_clear state modulus count
      valid conserved active beforeEnd iteration
  · exact congrArg
      (fun value : ArithmeticWindowPreservation.Retained modulus.size => value.2.2.2.1) retained
  · exact clean

/-- The actual advanced shift is nonzero, including the very first coefficient microstep. -/
theorem next_shift_nonzero (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    (nextFrame state modulus count valid conserved active beforeEnd iteration).shift ≠
      (0#modulus.size.size) := by
  intro zero
  have value := congrArg (fun word : BitVec modulus.size.size => word.toNat) zero
  change count + 1 = 0 at value
  omega

private theorem next_divisor_nonzero (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    (nextFrame state modulus count valid conserved active beforeEnd iteration).divisorLength ≠
      (0#modulus.size.size) := by
  intro zero
  have value := congrArg (fun word : BitVec modulus.size.size => word.toNat) zero
  change state.divisor.size = 0 at value
  have positiveSize : 0 < state.divisor.size := Nat.lt_size.mpr (by omega : 2 ^ 0 ≤ state.divisor)
  omega

/-- The real ordered control suffix enters phase four exactly when the actual quotient is empty. -/
theorem native_tail_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    let expected := nextFrame state modulus count valid conserved active beforeEnd iteration
    TerminalBoundary.step (ZeroShiftControl.step (NativeControl.step
      (GuardedShift.step true (ArithmeticBlocks.coefficientStep modulus.size
        (frame state modulus count valid conserved active beforeEnd iteration))))) =
      { expected with flags :=
        ⟨true, decide (expected.quotientLength = (0#modulus.size.size)),
          decide (expected.quotientLength = (0#modulus.size.size)), iteration⟩ } := by
  dsimp only
  rw [native_frame state modulus count valid conserved active beforeEnd iteration]
  exact CoefficientTail.tail_frame
    (nextFrame state modulus count valid conserved active beforeEnd iteration) rfl rfl rfl rfl
    (next_divisor_nonzero state modulus count valid conserved active beforeEnd iteration)
    (next_shift_nonzero state modulus count valid conserved active beforeEnd iteration)

/-- One complete native microstep consumes the actual quotient bit and advances phase three. -/
theorem microstep_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    let expected := nextFrame state modulus count valid conserved active beforeEnd iteration
    NativeMicrostep.step modulus.size
      (CoefficientConsumeFrame.frame state modulus count
        valid conserved active beforeEnd iteration) =
      { expected with flags :=
        ⟨true, decide (expected.quotientLength = (0#modulus.size.size)),
          decide (expected.quotientLength = (0#modulus.size.size)), iteration⟩ } := by
  dsimp only
  let original := CoefficientConsumeFrame.frame state modulus count
    valid conserved active beforeEnd iteration
  rw [NativeMicrostep.step, CoefficientTail.pre_shift_inactive modulus.size original rfl rfl,
    CoefficientTail.remainder_inactive modulus.size original rfl rfl,
    CoefficientConsumeAction.native_frame state modulus count
      valid conserved active beforeEnd iteration]
  exact native_tail_frame state modulus count valid conserved active beforeEnd iteration

end

end QuantumAlg.MAU.Inversion.SharedEEA.CoefficientAdvance
