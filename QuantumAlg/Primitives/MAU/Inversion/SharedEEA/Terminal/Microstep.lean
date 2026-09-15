/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Terminal.Position
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Deshift.Phase.Prelude
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Division.Tail
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Remainder.BlockLaws
import Mathlib.Logic.Function.Iterate

/-!
# Actual rotating terminal trajectory of the single native microstep

The complete native program continues to execute its source-ordered shift,
arithmetic selectors, phase gates, and boundary gates after the Euclidean
divisor becomes zero [LYL+26, sec_EEA/sub_opt.tex:37-84;
LYL+26, sec_EEA/sub_4phase.tex:119-128]. Its existing-wire clock records
every remaining rotation, including passage through zero in the low field.

The actual remainder selectors reject zero divisor length. The original
coefficient selectors are already disabled by Phase1 zero. The two real
terminal predicates inspect the complete clock, so neither phase exchange
nor word exchange occurs before complete wrap. This is a theorem about
`NativeMicrostep.step`, not an idle tail or another transition engine.
The independent schedule supplies the complete-clock bound internally.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.TerminalMicrostep

noncomputable section

open NumberTheory.SharedEEA TerminalPosition

private theorem pre_shift {width : Nat} (initial : Registers width) (count : Nat)
    (clean : initial.control = false) (first : initial.flags.first = false)
    (second : initial.flags.second = false) :
    GuardedShift.step false (frame initial count) = frame initial (count + 1) := by
  rw [GuardedShift.step_eq_source width false (frame initial count) clean,
    GuardedShift.sourceStep]
  change (if initial.flags.first = false then
    if initial.flags.second then GuardedShift.descending (GuardedShift.ascending _)
    else GuardedShift.ascending (frame initial count) else frame initial count) = _
  rw [first, if_pos rfl, second]
  change
    { frame initial count with
      firstWord := (PaddingClock.increment (pair initial count)).1
      secondWord := (initial.secondWord.rotateLeft count).rotateLeft 1
      shift := (PaddingClock.increment (pair initial count)).2 } = _
  rw [pair_increment, WordRotation.rotateLeft_comp]
  rfl

private theorem remainder_inactive {width : Nat} (state : Registers width)
    (clean : state.control = false) (second : state.flags.second = false)
    (finished : state.divisorLength = 0) :
    ArithmeticBlocks.remainderStep width state = state := by
  rw [ArithmeticBlocks.remainderStep_eq_source width state clean,
    RemainderBlockLaws.source_finished state finished]
  simp only [ArithmeticSign.remainderStep, second, Bool.and_false, Bool.xor_false]
  rw [← second]

private theorem control_inactive {width : Nat} (state : Registers width)
    (clean : state.control = false) (finished : state.divisorLength = 0) :
    NativeControl.step state = state := by
  have inactive : decide (state.divisorLength ≠ 0) = false :=
    decide_eq_false (fun nonzero => nonzero finished)
  rw [NativeControl.step_eq_sourceStep state clean, NativeControl.sourceStep, inactive]
  simp only [PhaseControl.update, Bool.and_false, Bool.false_eq_true, if_false]

private theorem zero_shift_inactive {width : Nat} (initial : Registers width) (count : Nat)
    (clean : initial.control = false) (finished : initial.divisorLength = 0)
    (positive : 0 < count) (within : count < 2 ^ (2 + width.size)) :
    ZeroShiftControl.step (frame initial count) = frame initial count := by
  rw [ZeroShiftControl.step_eq_sourceStep (frame initial count) clean,
    ZeroShiftControl.sourceStep, phase_condition_false initial count finished positive within]
  rfl

/-- Every actual terminal microstep advances the full physical clock and rotates the entire word. -/
theorem step_frame {width : Nat} (initial : Registers width) (count : Nat)
    (clean : initial.control = false) (first : initial.flags.first = false)
    (second : initial.flags.second = false) (finished : initial.divisorLength = 0)
    (within : count + 1 < 2 ^ (2 + width.size)) :
    NativeMicrostep.step width (frame initial count) = frame initial (count + 1) := by
  let after := frame initial (count + 1)
  rw [NativeMicrostep.step, pre_shift initial count clean first second,
    remainder_inactive after clean second finished,
    DeshiftPhasePrelude.quotient_inactive width after clean (first.trans second.symm),
    DivisionTail.coefficient_inactive width after clean first,
    DivisionTail.post_shift_inactive width after clean first,
    control_inactive after clean finished,
    zero_shift_inactive initial (count + 1) clean finished (by omega) within]
  exact TerminalBoundary.step_unselected after clean
    (boundary_condition_false initial (count + 1) finished (by omega) within)

/-- Ordinary iteration of the same actual action gives every full terminal position. -/
theorem iterate_frame {width : Nat} (initial : Registers width) (count : Nat)
    (clean : initial.control = false) (first : initial.flags.first = false)
    (second : initial.flags.second = false) (finished : initial.divisorLength = 0)
    (zero : ExtendedClockRegisters.clock initial = 0)
    (within : count < 2 ^ (2 + width.size)) :
    (NativeMicrostep.step width)^[count] initial = frame initial count := by
  induction count with
  | zero => exact (frame_zero initial zero).symm
  | succ count inductionHypothesis =>
      rw [Function.iterate_succ_apply', inductionHypothesis (by omega)]
      exact step_frame initial count clean first second finished within

/-- The emitted microstep has the exact normalized basis amplitude at each terminal position. -/
theorem program_apply_frame (width : Nat) (enough : 2 ≤ width.size)
    (initial : Registers width) (count : Nat)
    (clean : initial.control = false) (first : initial.flags.first = false)
    (second : initial.flags.second = false) (finished : initial.divisorLength = 0)
    (within : count + 1 < 2 ^ (2 + width.size)) :
    (NativeMicrostep.program width enough).applyNormalized
        (NormalizedVector.ket (R := Qubits (encoding width).width)
          ((encoding width).encode (frame initial count))) =
      NormalizedVector.ket (R := Qubits (encoding width).width)
        ((encoding width).encode (frame initial (count + 1))) := by
  rw [(NativeMicrostep.program_realizes width enough).apply_encoded_ket,
    step_frame initial count clean first second finished within]

end

end QuantumAlg.MAU.Inversion.SharedEEA.TerminalMicrostep
