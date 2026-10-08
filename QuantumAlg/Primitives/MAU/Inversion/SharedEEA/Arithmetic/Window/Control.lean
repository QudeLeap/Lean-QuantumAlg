/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Program
import all QuantumAlg.Components.Encoded.BitGates.Dirty.Control
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive

/-!
# Actual controlled arithmetic using the original arbitrary Iter bit

Each existing TTK elementary gate receives the actual retained Ctrl wire.
The three-control case borrows the original Iter bit and restores it on
every input through the four-Toffoli dirty-control construction
[G17, paper.tex:278-293]. Both wires are explicitly outside the operand
and Sign focus, and their final physical coordinates are those of the
original frame.

These actual lists provide the conditional arithmetic fragments of
[LYL+26, sec_EEA/sub_opt.tex:42-48,61-67]. They require neither clean Iter
nor clean Ctrl. Computing and uncomputing the source phase predicates
remains separate from the arithmetic action proved here.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowControl

noncomputable section

open EncodedBit ArithmeticWindowRegisters ArithmeticWindowEncoding
open ArithmeticWindowProgram

private theorem liftGate_eq_prodLeft {width : Nat} (window : Window width)
    (gate : GateSpec (Addition.TTK.overflowEncoding window.length)) :
    liftGate window gate = GateSpec.prodLeft (complementEncoding window) gate := by
  cases gate <;> rfl

private theorem liftGate_disjoint_right {width : Nat} (window : Window width)
    (observed : EncodedBit (complementEncoding window))
    (gate : GateSpec (Addition.TTK.overflowEncoding window.length)) :
    GateSpec.bitDisjoint (BinaryLabelEncoding.prodRightBit _ _ observed)
      (liftGate window gate) := by
  rw [liftGate_eq_prodLeft]
  exact GateSpec.bitDisjoint_prodLeft_rightBit _ _ observed gate

/-- Every actual arithmetic gate is disjoint from the original Ctrl wire. -/
theorem gates_control_disjoint {width : Nat} (window : Window width) (operation : Operation)
    (gate : GateSpec (groupedEncoding window))
    (present : gate ∈ ArithmeticWindowProgram.gates window operation) :
    GateSpec.bitDisjoint (ArithmeticWindowEncoding.controlBit window) gate := by
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp present
  exact liftGate_disjoint_right window _ original

/-- Every original arithmetic gate is disjoint from the arbitrary retained Iter wire. -/
theorem gates_work_disjoint {width : Nat} (window : Window width) (operation : Operation)
    (gate : GateSpec (groupedEncoding window))
    (present : gate ∈ ArithmeticWindowProgram.gates window operation) :
    GateSpec.bitDisjoint (workBit window) gate := by
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp present
  exact liftGate_disjoint_right window _ original

/-- The actual dirty-control expansion of the chosen TTK operation, using only original wires. -/
def gates {width : Nat} (window : Window width) (operation : Operation) :
    List (GateSpec (groupedEncoding window)) :=
  GateSpec.listWithDirtyControl (ArithmeticWindowEncoding.controlBit window) (workBit window)
    (ArithmeticWindowProgram.gates window operation)
    (gates_control_disjoint window operation) (gates_work_disjoint window operation)
    (ArithmeticWindowFullCoordinates.control_work_ne window)

/-- The complete selected action retains every complementary field, including arbitrary Iter. -/
theorem gates_step {width : Nat} (window : Window width) (operation : Operation)
    (state : Addition.TTK.OverflowRegisters window.length × Complement window) :
    GateSpec.stepList (gates window operation) state =
      if (ArithmeticWindowEncoding.controlBit window).get state then
        (focusStep operation state.1, state.2) else state := by
  rw [gates, GateSpec.listWithDirtyControl_step, ArithmeticWindowProgram.gates_step]

/-- Place the same actual controlled native list on the original physical frame. -/
def program {width : Nat} (window : Window width) (operation : Operation) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  ArithmeticWindowPlacement.place window
    (GateSpec.programList (QubitLayout.canonical _) .empty (gates window operation))

/-- Reassemble the complete output of the actual selected arithmetic. -/
def step {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) : Registers width :=
  ArithmeticWindowPlacement.placedStep window
    (fun pair => if (ArithmeticWindowEncoding.controlBit window).get pair then
      (focusStep operation pair.1, pair.2) else pair) state

/-- The actual whole-frame quantum program has the exact conditional basis amplitudes. -/
theorem program_realizes {width : Nat} (window : Window width) (operation : Operation) :
    UnitaryCircuit.Realizes (encoding width) (program window operation)
      (step window operation) := by
  have body : UnitaryCircuit.Realizes (groupedEncoding window)
      (GateSpec.programList (QubitLayout.canonical _) .empty (gates window operation))
      (fun pair : Addition.TTK.OverflowRegisters window.length × Complement window =>
        if (ArithmeticWindowEncoding.controlBit window).get pair then
          (focusStep operation pair.1, pair.2) else pair) :=
    GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
      (gates window operation) (gates_step window operation)
  exact ArithmeticWindowPlacement.place_realizes window body

/-- The original Ctrl selects the exact ungated arithmetic; its false branch is identity. -/
theorem step_eq_if {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    step window operation state =
      if state.control then ArithmeticWindowProgram.step window operation state else state := by
  rw [step, ArithmeticWindowPlacement.placedStep_eq]
  rw [ArithmeticWindowEncoding.controlBit_get]
  by_cases selected : state.control = true
  · rw [if_pos selected, if_pos selected]
    rw [ArithmeticWindowProgram.step, ArithmeticWindowPlacement.placedStep_eq]
  · rw [if_neg selected, if_neg selected]
    exact (grouping window).symm_apply_apply state

/-- Every bit outside the operand and Sign focus is restored, with no work-value premise. -/
theorem step_complement {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    (grouping window (step window operation state)).2 = (grouping window state).2 := by
  rw [step_eq_if]
  split
  · rw [ArithmeticWindowProgram.step_grouping]
  · rfl

/-- The entire Work2 operand window is retained as well as its already retained outside fields. -/
theorem step_source {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    (grouping window (step window operation state)).1.1.1 =
      (grouping window state).1.1.1 := by
  rw [step_eq_if]
  split
  · rw [ArithmeticWindowProgram.step_grouping, focusStep_source]
  · rfl

/-- The trace contains exactly the actual controlled elementary gates in their execution order. -/
theorem program_eventTrace {width : Nat} (window : Window width) (operation : Operation) :
    (program window operation).eventTrace =
      (gates window operation).map (GateSpec.event .empty) := by
  rw [program, ArithmeticWindowPlacement.place_eventTrace, GateSpec.programList_eventTrace]

/-- Exact unit depth is the real one-or-four-gate expansion of each original primitive. -/
theorem program_unitDepth {width : Nat} (window : Window width) (operation : Operation) :
    (program window operation).evaluatedEventDepth (fun _ => 1) =
      ((ArithmeticWindowProgram.gates window operation).map GateSpec.dirtyControlCount).sum := by
  rw [program, ArithmeticWindowPlacement.place_evaluatedEventDepth,
    GateSpec.programList_evaluatedEventDepth_unit, gates, GateSpec.listWithDirtyControl_length]

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowControl
