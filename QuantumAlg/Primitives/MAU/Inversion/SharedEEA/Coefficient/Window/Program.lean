/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Window.Coordinates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Control
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement

/-!
# Actual TTK coefficient arithmetic at the original little-endian wires

The complete existing TTK primitive lists are placed through the exact
coefficient grouping and physical coordinate map. Work1 is the source,
Work2 is the target, both use the actual little-endian prefix, and every
outside field includes its original arbitrary bits
[LYL+26, sec_EEA/sub_regshare.tex:17,20,263-264,291-294].

The selected versions use the existing Ctrl and borrow arbitrary Iter
through the already proved elementary dirty-control list. The actual
gate list and its trace are retained; the bit-order coordinate change
does not declare or execute an additional arithmetic primitive.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.CoefficientWindowProgram

noncomputable section

open EncodedBit ArithmeticWindowRegisters ArithmeticWindowEncoding
open ArithmeticWindowProgram

/-- Complete exact coefficient field and wire placement on the existing physical frame. -/
def placement {width : Nat} (window : Window width) :
    FullPlacement (groupedEncoding window) (encoding width) where
  grouping := CoefficientWindowOrientation.grouping window
  basis := CoefficientWindowOrientation.indexEquiv window
  basis_encode := CoefficientWindowOrientation.indexEquiv_encode window
  physicalIndex := CoefficientWindowCoordinates.physicalIndex window
  wire_injective := CoefficientWindowCoordinates.physicalIndex_injective window
  wire_within := CoefficientWindowCoordinates.physicalIndex_within window

/-- The actual ungated coefficient list, preserving its elementary gate order. -/
def program {width : Nat} (window : Window width) (operation : Operation) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  (placement window).place (GateSpec.programList (ArithmeticWindowProgram.gates window operation))
    (GateSpec.programList_physical_idx_subset_range _)

/-- Reassemble the complete coefficient arithmetic output and every retained original bit. -/
def step {width : Nat} (window : Window width) (operation : Operation) :
    Registers width → Registers width :=
  (placement window).step (fun pair => (focusStep operation pair.1, pair.2))

/-- Exact basis amplitudes of the same actual coefficient elementary program. -/
theorem program_realizes {width : Nat} (window : Window width) (operation : Operation) :
    UnitaryCircuit.Realizes (encoding width) (program window operation)
      (step window operation) := by
  have body : UnitaryCircuit.Realizes (groupedEncoding window)
      (GateSpec.programList (ArithmeticWindowProgram.gates window operation))
      (fun pair : Addition.TTK.OverflowRegisters window.length × Complement window =>
        (focusStep operation pair.1, pair.2)) :=
    GateSpec.realizesList_congrStep _ (ArithmeticWindowProgram.gates_step window operation)
  exact (placement window).place_realizes
    (body := GateSpec.programList (ArithmeticWindowProgram.gates window operation))
    (action := fun pair => (focusStep operation pair.1, pair.2))
    (GateSpec.programList_physical_idx_subset_range _) body

/-- The exact output includes oriented arithmetic and the complete original complement. -/
theorem step_grouping {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    CoefficientWindowOrientation.grouping window (step window operation state) =
      (focusStep operation (CoefficientWindowOrientation.grouping window state).1,
        (CoefficientWindowOrientation.grouping window state).2) :=
  (CoefficientWindowOrientation.grouping window).apply_symm_apply _

/-- The actual Ctrl-selected coefficient list, using arbitrary original Iter as restored work. -/
def controlledProgram {width : Nat} (window : Window width) (operation : Operation) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  (placement window).place (GateSpec.programList (ArithmeticWindowControl.gates window operation))
    (GateSpec.programList_physical_idx_subset_range _)

/-- Complete reassembly of the actual selected coefficient arithmetic. -/
def controlledStep {width : Nat} (window : Window width) (operation : Operation) :
    Registers width → Registers width :=
  (placement window).step
    (fun pair => if (ArithmeticWindowEncoding.controlBit window).get pair then
      (focusStep operation pair.1, pair.2) else pair)

/-- The selected program realizes the exact whole-frame action for arbitrary Ctrl and Iter. -/
theorem controlledProgram_realizes {width : Nat} (window : Window width) (operation : Operation) :
    UnitaryCircuit.Realizes (encoding width) (controlledProgram window operation)
      (controlledStep window operation) := by
  have body : UnitaryCircuit.Realizes (groupedEncoding window)
      (GateSpec.programList (ArithmeticWindowControl.gates window operation))
      (fun pair : Addition.TTK.OverflowRegisters window.length × Complement window =>
        if (ArithmeticWindowEncoding.controlBit window).get pair then
          (focusStep operation pair.1, pair.2) else pair) :=
    GateSpec.realizesList_congrStep _ (ArithmeticWindowControl.gates_step window operation)
  exact (placement window).place_realizes
    (body := GateSpec.programList (ArithmeticWindowControl.gates window operation))
    (action := fun pair => if (ArithmeticWindowEncoding.controlBit window).get pair then
      (focusStep operation pair.1, pair.2) else pair)
    (GateSpec.programList_physical_idx_subset_range _) body

private theorem control_get {width : Nat} (window : Window width) (state : Registers width) :
    (ArithmeticWindowEncoding.controlBit window).get
      (CoefficientWindowOrientation.grouping window state) = state.control := rfl

/-- Incoming Ctrl selects the same actual coefficient arithmetic, with an exact identity branch. -/
theorem controlledStep_eq_if {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    controlledStep window operation state =
      if state.control then step window operation state else state := by
  unfold controlledStep FullPlacement.step
  dsimp only
  change (CoefficientWindowOrientation.grouping window).symm
    (if (ArithmeticWindowEncoding.controlBit window).get
        (CoefficientWindowOrientation.grouping window state) then
      (focusStep operation (CoefficientWindowOrientation.grouping window state).1,
        (CoefficientWindowOrientation.grouping window state).2)
      else CoefficientWindowOrientation.grouping window state) = _
  rw [control_get]
  by_cases selected : state.control = true
  · rw [if_pos selected, if_pos selected]
    rfl
  · rw [if_neg selected, if_neg selected]
    exact (CoefficientWindowOrientation.grouping window).symm_apply_apply state

/-- The selected program keeps the complete original physical frame with no new helper wire. -/
theorem controlledProgram_physical {width : Nat} (window : Window width) (operation : Operation) :
    (controlledProgram window operation).physical_idx = List.range (encoding width).width :=
  (placement window).place_physical _ _

/-- Every real controlled TTK gate event is retained in its actual execution order. -/
theorem controlledProgram_eventTrace {width : Nat} (window : Window width)
    (operation : Operation) :
    (controlledProgram window operation).eventTrace =
      (ArithmeticWindowControl.gates window operation).map GateSpec.event := by
  rw [controlledProgram, FullPlacement.place_eventTrace, GateSpec.programList_eventTrace]

/-- Exact unit depth counts the actual dirty-control expansion of each existing TTK primitive. -/
theorem controlledProgram_unitDepth {width : Nat} (window : Window width)
    (operation : Operation) :
    (controlledProgram window operation).evaluatedEventDepth (fun _ => 1) =
      ((ArithmeticWindowProgram.gates window operation).map GateSpec.dirtyControlCount).sum := by
  rw [controlledProgram, FullPlacement.place_evaluatedEventDepth,
    GateSpec.programList_evaluatedEventDepth_unit, ArithmeticWindowControl.gates,
    GateSpec.listWithDirtyControl_length]

end

end QuantumAlg.MAU.Inversion.SharedEEA.CoefficientWindowProgram
