/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Selector.Gates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Schedule.Resources

/-!
# Literal instructions of the complete fixed arithmetic schedule

The same static enabled-key and window checks select each original native
instruction list. Concatenation follows the existing key list exactly, including
its order and every identity branch. Complete-frame action and ordered native
events agree with the original schedule for every Ctrl and Iter input value.
The original independent selector bound applies without an additional budget.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticSchedule

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit GateSpec ArithmeticWindowProgram ArithmeticSelectionKey ArithmeticInstruction

private def instructionGates (width : Nat) (instruction : Instruction)
    (selected : Key width (includeSign instruction)) : List (GateSpec (encoding width)) :=
  if enabled instruction selected then
    match selectedWindow instruction selected with
    | some window => ArithmeticSelector.gates window (operation instruction)
        (coefficient instruction) selected
    | none => []
  else []

private lemma instructionGates_step (width : Nat) (instruction : Instruction)
    (selected : Key width (includeSign instruction)) (state : Registers width) :
    stepList (instructionGates width instruction selected) state =
      ArithmeticInstruction.step width instruction selected state := by
  unfold instructionGates ArithmeticInstruction.step
  split
  · cases choice : selectedWindow instruction selected with
    | none => rfl
    | some window =>
        exact ArithmeticSelector.arithmeticSelector_gates_step window _ _ selected state
  · rfl

private lemma instructionGates_trace (width : Nat) (instruction : Instruction)
    (selected : Key width (includeSign instruction)) :
    (instructionGates width instruction selected).map (event .empty) =
      (ArithmeticInstruction.program width instruction selected).eventTrace := by
  unfold instructionGates ArithmeticInstruction.program
  split
  · cases choice : selectedWindow instruction selected with
    | none => rfl
    | some window =>
        exact ArithmeticSelector.arithmeticSelector_gates_trace window _ _ selected
  · rfl

private def listGates (width : Nat) (instruction : Instruction) :
    List (Key width (includeSign instruction)) → List (GateSpec (encoding width))
  | [] => []
  | selected :: rest => instructionGates width instruction selected ++
      listGates width instruction rest

private lemma listGates_step (width : Nat) (instruction : Instruction)
    (indices : List (Key width (includeSign instruction))) (state : Registers width) :
    stepList (listGates width instruction indices) state =
      indices.foldl
        (fun current selected => ArithmeticInstruction.step width instruction selected current)
        state := by
  induction indices generalizing state with
  | nil => rfl
  | cons selected rest ih =>
      rw [listGates, stepList_append, instructionGates_step, List.foldl_cons, ih]

private lemma listGates_trace (width : Nat) (instruction : Instruction)
    (indices : List (Key width (includeSign instruction))) :
    (listGates width instruction indices).map (event .empty) =
      (listProgram width instruction indices).eventTrace := by
  induction indices with
  | nil => rfl
  | cons selected rest ih =>
      rw [listGates, List.map_append, instructionGates_trace,
        listProgram, UnitaryCircuit.seq_eventTrace, ih]

/-- Every original enabled selector occurs once in the same fixed complete key order. -/
def gates (width : Nat) (instruction : Instruction) : List (GateSpec (encoding width)) :=
  listGates width instruction (keys width (includeSign instruction))

/-- The entire literal list has the original action on every complete incoming register label. -/
lemma arithmeticSchedule_gates_step (width : Nat) (instruction : Instruction)
    (state : Registers width) :
    stepList (gates width instruction) state = step width instruction state :=
  listGates_step width instruction (keys width (includeSign instruction)) state

/-- Compiling the emitted list preserves the complete coherent schedule on the supplied wires. -/
lemma arithmeticSchedule_gates_realizes (width : Nat) (instruction : Instruction)
    (layout : QubitLayout (encoding width).width) :
    UnitaryCircuit.Realizes (layout := layout) (encoding width)
      (programList layout .empty (gates width instruction)) environment (step width instruction) :=
  realizesList_congrStep layout .empty _ (arithmeticSchedule_gates_step width instruction)
    environment

/-- The complete actual predicate and arithmetic trace is retained in its original order. -/
lemma arithmeticSchedule_gates_trace (width : Nat) (instruction : Instruction) :
    (gates width instruction).map (event .empty) = (program width instruction).eventTrace :=
  listGates_trace width instruction (keys width (includeSign instruction))

/-- Flattening leaves every native multiplicity equal to the original actual circuit's pool. -/
lemma arithmeticSchedule_gates_eventCost (width : Nat) (instruction : Instruction) :
    ResourcePool.ofList ((gates width instruction).map (event .empty)) =
      (program width instruction).eventCost := by
  rw [arithmeticSchedule_gates_trace, UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- The same independent finite-selector envelope bounds the actual emitted instructions. -/
lemma arithmeticSchedule_gates_length_bound (width : Nat) (instruction : Instruction) :
    (gates width instruction).length ≤
      2 ^ ((4 * width.size + 2 + if includeSign instruction then 1 else 0) - 1) *
        ArithmeticScheduleResources.selectorBound width (includeSign instruction) := by
  have count := congrArg List.length (arithmeticSchedule_gates_trace width instruction)
  simp only [List.length_map] at count
  exact count.le.trans (ArithmeticScheduleResources.program_trace_le width instruction)

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticSchedule
