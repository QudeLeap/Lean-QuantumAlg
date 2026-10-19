/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Microstep
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ShiftResources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Schedule.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Terminal.Boundary.Resources

/-!
# Independent resource envelope for the same complete native shared-EEA microstep

All eight ordered blocks contribute their actual gate lists, including
every finite selector, dirty-work restoration, complete-clock update,
and terminal-aware boundary operation
[LYL+26, sec_EEA/sub_opt.tex:37-84]. The envelope is written in terms of
width arithmetic and the component envelopes before comparing it with
the native trace. It does not take a circuit's resource projection as
its budget, omit control-off occurrences, or claim the source's original
asymptotic constant for the revised physical implementation.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.MicrostepResources

noncomputable section

open ArithmeticInstruction

/-- Independent bound for one complete enumeration of the stated finite arithmetic instruction. -/
def instructionBound (width : Nat) (instruction : Instruction) : Nat :=
  2 ^ ((4 * width.size + 2 + if includeSign instruction then 1 else 0) - 1) *
    ArithmeticScheduleResources.selectorBound width (includeSign instruction)

/-- All actual sign-location selectors, followed by the complete low quotient update. -/
def signQuotientBound (width : Nat) : Nat :=
  2 ^ (width.size + (width.size + 1)) * (32 * width.size + 21) +
    ShiftResources.incrementCount width.size + 2 * width.size + 4

/-- Both original length predicates and the actual complete-clock/divisor conjunction. -/
def zeroShiftBound (width : Nat) : Nat :=
  2 * (NativeControl.conditionCount width +
    (10 * (width.size + 2 + width.size) + 1)) + 2

/-- Independent sum for every actual block of one fixed native iteration. -/
def bound (width : Nat) : Nat :=
  2 * ShiftResources.guardedBound width +
    instructionBound width .remainderSubtract + instructionBound width .remainderAddback + 3 +
    signQuotientBound width +
    instructionBound width .coefficientSubtract + instructionBound width .coefficientAdd + 1 +
    (2 * NativeControl.conditionCount width + 3) + zeroShiftBound width +
    TerminalBoundaryResources.boundaryBound width

/-- The same actual remainder list is bounded by its two full enumerations and three Sign gates. -/
lemma remainder_trace_le (width : Nat) :
    (ArithmeticBlocks.remainderProgram width).eventTrace.length ≤
      instructionBound width .remainderSubtract + instructionBound width .remainderAddback + 3 := by
  have subtract := ArithmeticScheduleResources.program_trace_le width .remainderSubtract
  have addback := ArithmeticScheduleResources.program_trace_le width .remainderAddback
  rw [ArithmeticBlocks.remainderProgram_eventTrace]
  simp only [List.length_append, ArithmeticSign.remainderProgram_eventTrace,
    List.length_cons, List.length_nil]
  unfold instructionBound
  omega

/-- The same actual coefficient list includes both enumerations and its real Sign CNOT. -/
lemma coefficient_trace_le (width : Nat) :
    (ArithmeticBlocks.coefficientProgram width).eventTrace.length ≤
      instructionBound width .coefficientSubtract + instructionBound width .coefficientAdd + 1 := by
  have subtract := ArithmeticScheduleResources.program_trace_le width .coefficientSubtract
  have add := ArithmeticScheduleResources.program_trace_le width .coefficientAdd
  rw [ArithmeticBlocks.coefficientProgram_eventTrace]
  simp only [List.length_append, ArithmeticSign.coefficientProgram_eventTrace,
    List.length_cons, List.length_nil]
  unfold instructionBound
  omega

/-- All Sign selectors and the actual quotient HRS gates satisfy the independent envelope. -/
lemma signQuotient_trace_le (width : Nat) :
    (SignQuotient.program width).eventTrace.length ≤ signQuotientBound width := by
  have selectors := SelectionResources.count_le_enumeration width
  rw [SignQuotient.program_eventTrace_length, ShiftResources.low_count, signQuotientBound]
  omega

/-- The actual terminal-aware zero-shift list charges both predicate passes and both phase CNOTs. -/
lemma zeroShift_trace_le (width : Nat) (enough : 2 ≤ width.size) :
    (ZeroShiftControl.program width enough).eventTrace.length ≤ zeroShiftBound width := by
  have conjunction := TerminalPredicate.clockDivisorGates_length_le width
  rw [ShiftResources.trace_count, ZeroShiftControl.program_eventCost_card,
    TerminalPredicate.gates_length, zeroShiftBound]
  unfold NativeControl.conditionCount TerminalPredicateLayout.sourceCount at *
  omega

/-- Every actual occurrence in the complete eight-block source order is covered. -/
lemma program_trace_le (width : Nat) (enough : 2 ≤ width.size) :
    (NativeMicrostep.program width enough).eventTrace.length ≤ bound width := by
  have firstShift := ShiftResources.guarded_trace_le width false
  have remainder := remainder_trace_le width
  have sign := signQuotient_trace_le width
  have coefficient := coefficient_trace_le width
  have lastShift := ShiftResources.guarded_trace_le width true
  have control : (NativeControl.program width enough).eventTrace.length =
      2 * NativeControl.conditionCount width + 3 :=
    (ShiftResources.trace_count _).trans (NativeControl.program_eventCost_card width enough)
  have zeroShift := zeroShift_trace_le width enough
  have boundary : (TerminalBoundary.program width enough).eventTrace.length ≤
      TerminalBoundaryResources.boundaryBound width :=
    (ShiftResources.trace_count _).le.trans (TerminalBoundaryResources.eventCount_le width enough)
  rw [NativeMicrostep.program_eventTrace]
  simp only [List.length_append]
  unfold bound
  omega

/-- The event pool and strict unit depth are both derived from that same actual native microstep. -/
lemma program_resources (width : Nat) (enough : 2 ≤ width.size) :
    (NativeMicrostep.program width enough).eventCost.card ≤ bound width ∧
      (NativeMicrostep.program width enough).evaluatedEventDepth (fun _ => 1) ≤ bound width := by
  have count := (ShiftResources.trace_count (NativeMicrostep.program width enough)).symm.le.trans
    (program_trace_le width enough)
  exact ⟨count, (ShiftResources.unitDepth_le_count _).trans count⟩

end

end QuantumAlg.MAU.Inversion.SharedEEA.MicrostepResources
