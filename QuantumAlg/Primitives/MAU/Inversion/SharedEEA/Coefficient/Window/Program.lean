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

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit ArithmeticWindowRegisters ArithmeticWindowEncoding
open ArithmeticWindowProgram

/-- Complete exact coefficient field and wire placement on the existing physical frame. -/
def placement {width : Nat} (window : Window width) :
    FullPlacement (groupedEncoding window) (encoding width) :=
  FullPlacement.ofWires (groupedEncoding window) (encoding width)
    (groupedEncoding_surjective window) (encoding_surjective width)
    (CoefficientWindowCoordinates.wireEquiv window)

private def focusBit {width : Nat} (window : Window width)
    (bit : EncodedBit (Addition.TTK.overflowEncoding window.length)) :
    EncodedBit (groupedEncoding window) :=
  BinaryLabelEncoding.prodLeftBit _ _ bit

private lemma source_read {width : Nat} (window : Window width)
    (index : Fin window.length) (state : Registers width) :
    (Addition.TTK.withOverflowBit (Addition.TTK.leftBit window.length index)).get
      ((placement window).grouping state).1 =
        (firstWordBit width (CoefficientWindowOrientation.windowIndex window index)).get state := by
  let bit := focusBit window
    (Addition.TTK.withOverflowBit (Addition.TTK.leftBit window.length index))
  have same : CoefficientWindowCoordinates.wireEquiv window bit.wire =
      (firstWordBit width (CoefficientWindowOrientation.windowIndex window index)).wire := by
    apply Fin.ext
    change CoefficientWindowCoordinates.physicalIndex window bit.wire.val = _
    change CoefficientWindowCoordinates.physicalIndex window
      (window.length - 1 - index.val) = window.above + index.val
    exact CoefficientWindowCoordinates.physicalIndex_source window index
  exact FullPlacement.ofWires_read (groupedEncoding window) (encoding width)
    (groupedEncoding_surjective window) (encoding_surjective width)
    (CoefficientWindowCoordinates.wireEquiv window) bit _ same state

private lemma target_read {width : Nat} (window : Window width)
    (index : Fin window.length) (state : Registers width) :
    (Addition.TTK.withOverflowBit (Addition.TTK.rightBit window.length index)).get
      ((placement window).grouping state).1 =
        (secondWordBit width
          (CoefficientWindowOrientation.windowIndex window index)).get state := by
  let bit := focusBit window
    (Addition.TTK.withOverflowBit (Addition.TTK.rightBit window.length index))
  have same : CoefficientWindowCoordinates.wireEquiv window bit.wire =
      (secondWordBit width (CoefficientWindowOrientation.windowIndex window index)).wire := by
    apply Fin.ext
    change CoefficientWindowCoordinates.physicalIndex window bit.wire.val = _
    change CoefficientWindowCoordinates.physicalIndex window
      (window.length + (window.length - 1 - index.val)) =
        width + 3 + (window.above + index.val)
    simpa only [Nat.add_assoc] using
      CoefficientWindowCoordinates.physicalIndex_target window index
  exact FullPlacement.ofWires_read (groupedEncoding window) (encoding width)
    (groupedEncoding_surjective window) (encoding_surjective width)
    (CoefficientWindowCoordinates.wireEquiv window) bit _ same state

private lemma sign_read {width : Nat} (window : Window width)
    (state : Registers width) :
    (Addition.TTK.overflowBit window.length).get ((placement window).grouping state).1 =
      (signBit width).get state := by
  let bit := focusBit window (Addition.TTK.overflowBit window.length)
  have same : CoefficientWindowCoordinates.wireEquiv window bit.wire =
      (signBit width).wire := by
    apply Fin.ext
    change CoefficientWindowCoordinates.physicalIndex window bit.wire.val = _
    change CoefficientWindowCoordinates.physicalIndex window
      (window.length + window.length) =
      (signBit width).wire.val
    simpa only [two_mul] using CoefficientWindowCoordinates.physicalIndex_sign window
  exact FullPlacement.ofWires_read (groupedEncoding window) (encoding width)
    (groupedEncoding_surjective window) (encoding_surjective width)
    (CoefficientWindowCoordinates.wireEquiv window) bit _ same state

private lemma focus_grouping {width : Nat} (window : Window width)
    (state : Registers width) :
    ((placement window).grouping state).1 =
      (CoefficientWindowOrientation.grouping window state).1 := by
  apply Prod.ext
  · apply Prod.ext
    · apply (BinaryBasis.bigEndianEquiv window.length).symm.injective
      funext index
      apply finTwoEquiv.injective
      simp only [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply]
      have actual := (source_read window index.rev state).trans
        (CoefficientWindowOrientation.grouping_source_bit window index.rev state).symm
      rw [Addition.TTK.ttkWithOverflowBit_get, Addition.TTK.ttkWithOverflowBit_get,
        Addition.TTK.ttkLeftBit_get, Addition.TTK.ttkLeftBit_get] at actual
      exact actual
    · apply (BinaryBasis.bigEndianEquiv window.length).symm.injective
      funext index
      apply finTwoEquiv.injective
      simp only [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply]
      have actual := (target_read window index.rev state).trans
        (CoefficientWindowOrientation.grouping_target_bit window index.rev state).symm
      rw [Addition.TTK.ttkWithOverflowBit_get, Addition.TTK.ttkWithOverflowBit_get,
        Addition.TTK.ttkRightBit_get, Addition.TTK.ttkRightBit_get] at actual
      exact actual
  · exact (sign_read window state).trans
      (CoefficientWindowOrientation.grouping_sign window state).symm

private lemma complement_grouping {width : Nat} (window : Window width)
    (state : Registers width) :
    ((placement window).grouping state).2 =
      (CoefficientWindowOrientation.grouping window state).2 := by
  have fixed (index : Fin (groupedEncoding window).width)
      (outside : 2 * window.length + 1 ≤ index.val) :
      CoefficientWindowCoordinates.wireEquiv window index =
        ArithmeticWindowFullCoordinates.wireEquiv window index := by
    apply Fin.ext
    change CoefficientWindowCoordinates.physicalIndex window index.val =
      ArithmeticWindowFullCoordinates.physicalIndex window index.val
    rw [CoefficientWindowCoordinates.physicalIndex,
      CoefficientWindowCoordinates.operandSlots, if_neg (by omega)]
  exact (ArithmeticWindowPlacement.complement_ofWires_fixed window
    (CoefficientWindowCoordinates.wireEquiv window) fixed state).trans
    (CoefficientWindowOrientation.grouping_complement window state).symm

/-- The reflected physical wire map reconstructs the exact coefficient field grouping. -/
lemma placement_grouping {width : Nat} (window : Window width)
    (state : Registers width) :
    (placement window).grouping state = CoefficientWindowOrientation.grouping window state := by
  apply Prod.ext
  · exact focus_grouping window state
  · exact complement_grouping window state

lemma placement_grouping_equiv {width : Nat} (window : Window width) :
    (placement window).grouping = CoefficientWindowOrientation.grouping window :=
  Equiv.ext (placement_grouping window)

/-- The actual ungated coefficient list, preserving its elementary gate order. -/
def program {width : Nat} (window : Window width) (operation : Operation) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (placement window).place
    (GateSpec.programList (QubitLayout.canonical _) .empty
      (ArithmeticWindowProgram.gates window operation))

/-- Reassemble the complete coefficient arithmetic output and every retained original bit. -/
def step {width : Nat} (window : Window width) (operation : Operation) :
    Registers width → Registers width :=
  (placement window).step (fun pair => (focusStep operation pair.1, pair.2))

/-- Exact basis amplitudes of the same actual coefficient elementary program. -/
lemma program_realizes {width : Nat} (window : Window width) (operation : Operation) :
    UnitaryCircuit.Realizes (encoding width) (program window operation) environment
      (step window operation) := by
  have body : UnitaryCircuit.Realizes (groupedEncoding window)
      (GateSpec.programList (QubitLayout.canonical _) .empty
        (ArithmeticWindowProgram.gates window operation)) environment
      (fun pair : Addition.TTK.OverflowRegisters window.length × Complement window =>
        (focusStep operation pair.1, pair.2)) :=
    GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
      (ArithmeticWindowProgram.gates_step window operation) environment
  exact (placement window).place_realizes body

/-- The exact output includes oriented arithmetic and the complete original complement. -/
lemma step_grouping {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    CoefficientWindowOrientation.grouping window (step window operation state) =
      (focusStep operation (CoefficientWindowOrientation.grouping window state).1,
      (CoefficientWindowOrientation.grouping window state).2) := by
  rw [step, FullPlacement.step, placement_grouping_equiv]
  exact (CoefficientWindowOrientation.grouping window).apply_symm_apply _

/-- The actual Ctrl-selected coefficient list, using arbitrary original Iter as restored work. -/
def controlledProgram {width : Nat} (window : Window width) (operation : Operation) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (placement window).place
    (GateSpec.programList (QubitLayout.canonical _) .empty
      (ArithmeticWindowControl.gates window operation))

/-- Complete reassembly of the actual selected coefficient arithmetic. -/
def controlledStep {width : Nat} (window : Window width) (operation : Operation) :
    Registers width → Registers width :=
  (placement window).step
    (fun pair => if (ArithmeticWindowEncoding.controlBit window).get pair then
      (focusStep operation pair.1, pair.2) else pair)

/-- The selected program realizes the exact whole-frame action for arbitrary Ctrl and Iter. -/
lemma controlledProgram_realizes {width : Nat} (window : Window width) (operation : Operation) :
    UnitaryCircuit.Realizes (encoding width) (controlledProgram window operation) environment
      (controlledStep window operation) := by
  have body : UnitaryCircuit.Realizes (groupedEncoding window)
      (GateSpec.programList (QubitLayout.canonical _) .empty
        (ArithmeticWindowControl.gates window operation)) environment
      (fun pair : Addition.TTK.OverflowRegisters window.length × Complement window =>
        if (ArithmeticWindowEncoding.controlBit window).get pair then
          (focusStep operation pair.1, pair.2) else pair) :=
    GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
      (ArithmeticWindowControl.gates_step window operation) environment
  exact (placement window).place_realizes body

private lemma control_get {width : Nat} (window : Window width) (state : Registers width) :
    (ArithmeticWindowEncoding.controlBit window).get
      (CoefficientWindowOrientation.grouping window state) = state.control := rfl

/-- Incoming Ctrl selects the same actual coefficient arithmetic, with an exact identity branch. -/
lemma controlledStep_eq_if {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    controlledStep window operation state =
      if state.control then step window operation state else state := by
  unfold controlledStep FullPlacement.step
  rw [placement_grouping_equiv]
  dsimp only
  rw [control_get]
  by_cases selected : state.control = true
  · rw [if_pos selected, if_pos selected]
    rw [step, FullPlacement.step, placement_grouping_equiv]
  · rw [if_neg selected, if_neg selected]
    exact (CoefficientWindowOrientation.grouping window).symm_apply_apply state

/-- Every real controlled TTK gate event is retained in its actual execution order. -/
lemma controlledProgram_eventTrace {width : Nat} (window : Window width)
    (operation : Operation) :
    (controlledProgram window operation).eventTrace =
      (ArithmeticWindowControl.gates window operation).map (GateSpec.event .empty) := by
  rw [controlledProgram, FullPlacement.place_eventTrace, GateSpec.programList_eventTrace]

/-- Exact unit depth counts the actual dirty-control expansion of each existing TTK primitive. -/
lemma controlledProgram_unitDepth {width : Nat} (window : Window width)
    (operation : Operation) :
    (controlledProgram window operation).evaluatedEventDepth (fun _ => 1) =
      ((ArithmeticWindowProgram.gates window operation).map GateSpec.dirtyControlCount).sum := by
  rw [controlledProgram, FullPlacement.place_evaluatedEventDepth,
    GateSpec.programList_evaluatedEventDepth_unit, ArithmeticWindowControl.gates,
    GateSpec.listWithDirtyControl_length]

end

end QuantumAlg.MAU.Inversion.SharedEEA.CoefficientWindowProgram
