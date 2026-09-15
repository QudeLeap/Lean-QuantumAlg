/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Schedule
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Sign

/-!
# Actual complete remainder and coefficient source arithmetic blocks

The remainder block executes signed subtraction, the actual phase-2 Sign
complement, and selected low add-back in that order
[LYL+26, sec_EEA/sub_opt.tex:43-48]. The coefficient block executes its
selected low subtraction, actual Phase1 Sign complement, and signed
addition in order [LYL+26, sec_EEA/sub_opt.tex:61-66].

All selections execute the complete finite native schedules and their real
predicate cleanup. Whole-frame realization holds for arbitrary incoming
Ctrl. Source refinement uses only the Ctrl-zero invariant established by
the algorithm's own preparation and retained by each previous actual block.
These arithmetic blocks do not include pre/post shifts or the interposed
Sign/quotient exchange, which remain separately executed source operations.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticBlocks

noncomputable section

/-- The actual remainder signed subtraction, Sign complement, and selected add-back. -/
def remainderProgram (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  (ArithmeticSchedule.program width .remainderSubtract).seq
    ((ArithmeticSign.remainderProgram width).seq
      (ArithmeticSchedule.program width .remainderAddback))

/-- Complete full-frame action of those actual three remainder programs. -/
def remainderStep (width : Nat) (state : Registers width) : Registers width :=
  ArithmeticSchedule.step width .remainderAddback
    (ArithmeticSign.remainderStep (ArithmeticSchedule.step width .remainderSubtract state))

/-- The same ordered remainder specification in the actual current finite register fields. -/
def remainderSource {width : Nat} (state : Registers width) : Registers width :=
  ArithmeticInstruction.sourceStep .remainderAddback
    (ArithmeticSign.remainderStep (ArithmeticInstruction.sourceStep .remainderSubtract state))

/-- The full actual remainder block realizes its exact action for every original frame label. -/
theorem remainderProgram_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (remainderProgram width) (remainderStep width) :=
  (ArithmeticSchedule.program_realizes width .remainderSubtract).seq
    ((ArithmeticSign.remainderProgram_realizes width).seq
      (ArithmeticSchedule.program_realizes width .remainderAddback))

/-- Every actual remainder instruction and its cleanup preserves the original Ctrl. -/
theorem remainderStep_control (width : Nat) (state : Registers width) :
    (remainderStep width state).control = state.control := by
  rw [remainderStep, ArithmeticSchedule.step_control, ArithmeticSign.remainderStep_control,
    ArithmeticSchedule.step_control]

/-- Arbitrary original Iter survives the whole remainder block, including all equality gates. -/
theorem remainderStep_iteration (width : Nat) (state : Registers width) :
    (remainderStep width state).flags.iteration = state.flags.iteration := by
  rw [remainderStep, ArithmeticSchedule.step_iteration]
  change (ArithmeticSchedule.step width .remainderSubtract state).flags.iteration = _
  exact ArithmeticSchedule.step_iteration width .remainderSubtract state

private theorem source_control (width : Nat) (instruction : ArithmeticInstruction.Instruction)
    (state : Registers width) (clean : state.control = false) :
    (ArithmeticInstruction.sourceStep instruction state).control = false := by
  rw [← ArithmeticSchedule.step_eq_source width instruction state clean,
    ArithmeticSchedule.step_control]
  exact clean

/-- The initialized actual remainder block equals the independent source's ordered operations. -/
theorem remainderStep_eq_source (width : Nat) (state : Registers width)
    (clean : state.control = false) : remainderStep width state = remainderSource state := by
  have afterSubtraction := source_control width .remainderSubtract state clean
  have afterSign :
      (ArithmeticSign.remainderStep
        (ArithmeticInstruction.sourceStep .remainderSubtract state)).control = false :=
    (ArithmeticSign.remainderStep_control _).trans afterSubtraction
  rw [remainderStep, remainderSource,
    ArithmeticSchedule.step_eq_source width .remainderSubtract state clean,
    ArithmeticSchedule.step_eq_source width .remainderAddback _ afterSign]

/-- The actual coefficient low subtraction, Sign complement, and signed addition. -/
def coefficientProgram (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  (ArithmeticSchedule.program width .coefficientSubtract).seq
    ((ArithmeticSign.coefficientProgram width).seq
      (ArithmeticSchedule.program width .coefficientAdd))

/-- Complete frame action of the actual three coefficient programs. -/
def coefficientStep (width : Nat) (state : Registers width) : Registers width :=
  ArithmeticSchedule.step width .coefficientAdd
    (ArithmeticSign.coefficientStep (ArithmeticSchedule.step width .coefficientSubtract state))

/-- The source coefficient block in its explicit actual current-field execution order. -/
def coefficientSource {width : Nat} (state : Registers width) : Registers width :=
  ArithmeticInstruction.sourceStep .coefficientAdd
    (ArithmeticSign.coefficientStep (ArithmeticInstruction.sourceStep .coefficientSubtract state))

/-- Actual complete coefficient realization includes every selector and inverse predicate. -/
theorem coefficientProgram_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (coefficientProgram width) (coefficientStep width) :=
  (ArithmeticSchedule.program_realizes width .coefficientSubtract).seq
    ((ArithmeticSign.coefficientProgram_realizes width).seq
      (ArithmeticSchedule.program_realizes width .coefficientAdd))

/-- The original Ctrl is restored by all coefficient arithmetic and Sign gates. -/
theorem coefficientStep_control (width : Nat) (state : Registers width) :
    (coefficientStep width state).control = state.control := by
  rw [coefficientStep, ArithmeticSchedule.step_control, ArithmeticSign.coefficientStep_control,
    ArithmeticSchedule.step_control]

/-- The coefficient block retains arbitrary original Iter through all borrowed-work operations. -/
theorem coefficientStep_iteration (width : Nat) (state : Registers width) :
    (coefficientStep width state).flags.iteration = state.flags.iteration := by
  rw [coefficientStep, ArithmeticSchedule.step_iteration]
  change (ArithmeticSchedule.step width .coefficientSubtract state).flags.iteration = _
  exact ArithmeticSchedule.step_iteration width .coefficientSubtract state

/-- Its initialized actual execution equals the source's ordered coefficient operations. -/
theorem coefficientStep_eq_source (width : Nat) (state : Registers width)
    (clean : state.control = false) : coefficientStep width state = coefficientSource state := by
  have afterSubtraction := source_control width .coefficientSubtract state clean
  have afterSign :
      (ArithmeticSign.coefficientStep
        (ArithmeticInstruction.sourceStep .coefficientSubtract state)).control = false :=
    (ArithmeticSign.coefficientStep_control _).trans afterSubtraction
  rw [coefficientStep, coefficientSource,
    ArithmeticSchedule.step_eq_source width .coefficientSubtract state clean,
    ArithmeticSchedule.step_eq_source width .coefficientAdd _ afterSign]

/-- Ordered remainder events retain both schedules and the intervening native Sign gates. -/
theorem remainderProgram_eventTrace (width : Nat) :
    (remainderProgram width).eventTrace =
      (ArithmeticSchedule.program width .remainderSubtract).eventTrace ++
      (ArithmeticSign.remainderProgram width).eventTrace ++
      (ArithmeticSchedule.program width .remainderAddback).eventTrace := by
  rw [remainderProgram, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.seq_eventTrace,
    List.append_assoc]

/-- Ordered coefficient events include the actual intervening Sign CNOT. -/
theorem coefficientProgram_eventTrace (width : Nat) :
    (coefficientProgram width).eventTrace =
      (ArithmeticSchedule.program width .coefficientSubtract).eventTrace ++
      (ArithmeticSign.coefficientProgram width).eventTrace ++
      (ArithmeticSchedule.program width .coefficientAdd).eventTrace := by
  rw [coefficientProgram, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.seq_eventTrace,
    List.append_assoc]

/-- Strict actual remainder depth includes the three emitted Sign-control gates. -/
theorem remainderProgram_unitDepth (width : Nat) :
    (remainderProgram width).evaluatedEventDepth (fun _ => 1) =
      (ArithmeticSchedule.program width .remainderSubtract).evaluatedEventDepth (fun _ => 1) +
      (3 + (ArithmeticSchedule.program width .remainderAddback).evaluatedEventDepth
        (fun _ => 1)) := by
  rw [remainderProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq, ArithmeticSign.remainderProgram_unitDepth]

/-- Strict actual coefficient depth includes its one emitted Sign CNOT. -/
theorem coefficientProgram_unitDepth (width : Nat) :
    (coefficientProgram width).evaluatedEventDepth (fun _ => 1) =
      (ArithmeticSchedule.program width .coefficientSubtract).evaluatedEventDepth (fun _ => 1) +
      (1 + (ArithmeticSchedule.program width .coefficientAdd).evaluatedEventDepth
        (fun _ => 1)) := by
  rw [coefficientProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq, ArithmeticSign.coefficientProgram_unitDepth]

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticBlocks
