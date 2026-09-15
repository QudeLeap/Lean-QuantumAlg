/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Schedule
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Resources

/-!
# Actual arithmetic selector schedule after complete coefficient comparison

The actual equality layout reads all four existing length words, the two
phase bits, and Sign only when the arithmetic retains it. Reading the
existing divisor boundary permits the full aligned coefficient comparison
[LYL+26, sec_EEA/sub_regshare.tex:263-264,297-300]. No quantum register is
allocated for finite enumeration keys.

The bounds below count both real predicate lists and the actual controlled
TTK arithmetic for every emitted selector, including cleanup of arbitrary
Iter. Invalid windows emit the existing empty identity. These are bounds
for the present finite native schedule, not the paper's original whole-EEA
asymptotic count or a claim about unproved terminal dispatch.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticScheduleResources

noncomputable section

open EncodedBit ArithmeticWindowRegisters ArithmeticWindowProgram ArithmeticWindowPreservation
open ArithmeticSelectionKey ArithmeticInstruction

/-- Uniform elementary-gate bound for both predicates and the actual full-word arithmetic. -/
def selectorBound (width : Nat) (includeSign : Bool) : Nat :=
  20 * ArithmeticSelectionLayout.sourceCount width includeSign + 28 * (width + 3) + 10

/-- The selector trace includes both full pattern computations and the controlled TTK list. -/
theorem selector_trace_le {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) (selected : Key width (readsSign operation)) :
    (ArithmeticSelector.program window operation coefficient selected).eventTrace.length ≤
      selectorBound width (readsSign operation) := by
  rw [ArithmeticSelector.program_eventTrace]
  simp only [List.length_append, List.length_map, List.length_reverse]
  have predicate := ArithmeticSelectionPredicate.gates_length_le width
    (readsSign operation) selected
  have body := ArithmeticWindowResources.controlledGates_length_le_frame window operation
  unfold selectorBound
  omega

/-- Unit event depth of this strictly sequential selector is its actual emitted event count. -/
theorem selector_depth_eq_trace {width : Nat} (window : Window width) (operation : Operation)
    (coefficient : Bool) (selected : Key width (readsSign operation)) :
    (ArithmeticSelector.program window operation coefficient selected).evaluatedEventDepth
        (fun _ => 1) =
      (ArithmeticSelector.program window operation coefficient selected).eventTrace.length := by
  rw [ArithmeticSelector.program_eventTrace]
  cases coefficient <;>
    simp only [ArithmeticSelector.program, ArithmeticSelector.controlledBody,
      Bool.false_eq_true, if_false, if_true, UnitaryCircuit.evaluatedEventDepth_seq,
      ArithmeticSelectionPredicate.program_unitDepth,
      ArithmeticWindowResources.remainder_unitDepth,
      ArithmeticWindowResources.coefficient_unitDepth,
      GateSpec.programList_evaluatedEventDepth_unit,
      List.length_append, List.length_map, List.length_reverse, Nat.add_assoc]

/-- Every actual instruction has the same bound, including disabled and invalid-window keys. -/
theorem instruction_trace_le (width : Nat) (instruction : Instruction)
    (selected : Key width (includeSign instruction)) :
    (ArithmeticInstruction.program width instruction selected).eventTrace.length ≤
      selectorBound width (includeSign instruction) := by
  unfold ArithmeticInstruction.program
  split
  · cases choice : selectedWindow instruction selected with
    | none => exact Nat.zero_le _
    | some window =>
        exact selector_trace_le window (operation instruction) (coefficient instruction) selected
  · exact Nat.zero_le _

/-- The strict depth of each emitted instruction is its actual event trace length. -/
theorem instruction_depth_eq_trace (width : Nat) (instruction : Instruction)
    (selected : Key width (includeSign instruction)) :
    (ArithmeticInstruction.program width instruction selected).evaluatedEventDepth (fun _ => 1) =
      (ArithmeticInstruction.program width instruction selected).eventTrace.length := by
  unfold ArithmeticInstruction.program
  split
  · cases choice : selectedWindow instruction selected with
    | none => rfl
    | some window =>
        exact selector_depth_eq_trace window (operation instruction)
          (coefficient instruction) selected
  · rfl

private theorem list_trace_le (width : Nat) (instruction : Instruction)
    (indices : List (Key width (includeSign instruction))) :
    (indices.flatMap fun selected =>
      (ArithmeticInstruction.program width instruction selected).eventTrace).length ≤
        indices.length * selectorBound width (includeSign instruction) := by
  induction indices with
  | nil => simp
  | cons selected rest ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
      have current := instruction_trace_le width instruction selected
      omega

private theorem list_depth_eq_trace (width : Nat) (instruction : Instruction)
    (indices : List (Key width (includeSign instruction))) :
    (ArithmeticSchedule.listProgram width instruction indices).evaluatedEventDepth (fun _ => 1) =
      (ArithmeticSchedule.listProgram width instruction indices).eventTrace.length := by
  induction indices with
  | nil => rfl
  | cons selected rest ih =>
      rw [ArithmeticSchedule.listProgram, UnitaryCircuit.evaluatedEventDepth_seq,
        UnitaryCircuit.seq_eventTrace, List.length_append,
        instruction_depth_eq_trace, ih]

/-- The exact revised enumeration counts all four real length words and actual source flags. -/
theorem selector_count (width : Nat) (instruction : Instruction) :
    (ArithmeticSelectionKey.keys width (includeSign instruction)).length =
      2 ^ (4 * width.size + 2 + if includeSign instruction then 1 else 0) :=
  ArithmeticSchedule.selector_count width instruction

/-- Actual trace size includes every emitted selector and both predicate computations. -/
theorem program_trace_le (width : Nat) (instruction : Instruction) :
    (ArithmeticSchedule.program width instruction).eventTrace.length ≤
      2 ^ (4 * width.size + 2 + if includeSign instruction then 1 else 0) *
        selectorBound width (includeSign instruction) := by
  rw [ArithmeticSchedule.program_eventTrace]
  have actual := list_trace_le width instruction
    (ArithmeticSelectionKey.keys width (includeSign instruction))
  rw [selector_count] at actual
  exact actual

/-- Strict unit duration depth counts the same actual sequential native trace. -/
theorem program_depth_eq_trace (width : Nat) (instruction : Instruction) :
    (ArithmeticSchedule.program width instruction).evaluatedEventDepth (fun _ => 1) =
      (ArithmeticSchedule.program width instruction).eventTrace.length :=
  list_depth_eq_trace width instruction
    (ArithmeticSelectionKey.keys width (includeSign instruction))

/-- The independent selector envelope therefore bounds the actual complete native depth. -/
theorem program_depth_le (width : Nat) (instruction : Instruction) :
    (ArithmeticSchedule.program width instruction).evaluatedEventDepth (fun _ => 1) ≤
      2 ^ (4 * width.size + 2 + if includeSign instruction then 1 else 0) *
        selectorBound width (includeSign instruction) := by
  rw [program_depth_eq_trace]
  exact program_trace_le width instruction

/-- The same trace derives the literal resource pool; no independent cost witness is accepted. -/
theorem program_pool (width : Nat) (instruction : Instruction) :
    (ArithmeticSchedule.program width instruction).eventCost = ResourcePool.ofList
      (ArithmeticSchedule.program width instruction).eventTrace :=
  (UnitaryCircuit.ofList_eventTrace_eq_eventCost _).symm

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticScheduleResources
