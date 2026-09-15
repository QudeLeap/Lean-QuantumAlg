/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Placement
import all QuantumAlg.Primitives.MAU.Addition.TTK.Subtraction
import all QuantumAlg.Primitives.MAU.Addition.TTK.Overflow.Readout

/-!
# Actual ancilla-free TTK arithmetic on the two existing work-word windows

The complete elementary TTK addition or inverse-subtraction list is lifted
beside the explicitly retained complementary fields and physically placed
on the original frame. Low arithmetic retains Sign; signed arithmetic
xors the actual carry or borrow into arbitrary incoming Sign
[TTK09, qic-loglogaddition-quant.tex:285-318;
HRS16, paper.tex:217-225].

Every mode preserves the Work2 source window and the entire complement,
including all wrapped coefficient bits and the existing Iter and Ctrl.
These are the actual ungated arithmetic fragments needed by the shared
source blocks [LYL+26, sec_EEA/sub_opt.tex:42-48,61-67]. Selection and the
arbitrary-work control decomposition are subsequent native gate lists.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowProgram

noncomputable section

open EncodedBit ArithmeticWindowRegisters ArithmeticWindowEncoding

/-- The four actual source arithmetic instructions, with or without updating Sign. -/
inductive Operation where
  | addLow
  | subtractLow
  | addSigned
  | subtractSigned
deriving DecidableEq

/-- Existing exact TTK elementary gates; subtraction is its actual inverse sequence. -/
def focusGates (length : Nat) : Operation →
    List (GateSpec (Addition.TTK.overflowEncoding length))
  | .addLow => (Addition.TTK.lowRippleGates length).map Addition.TTK.withOverflowGate
  | .subtractLow => (Addition.TTK.subtractionGates length).map Addition.TTK.withOverflowGate
  | .addSigned => Addition.TTK.overflowGates length
  | .subtractSigned => Addition.TTK.overflowSubtractionGates length

/-- Independent complete finite arithmetic semantics for those actual TTK programs. -/
def focusStep {length : Nat} (operation : Operation)
    (state : Addition.TTK.OverflowRegisters length) :
    Addition.TTK.OverflowRegisters length :=
  match operation with
  | .addLow => (Addition.TTK.lowOutput state.1, state.2)
  | .subtractLow => (Addition.TTK.subtractionOutput state.1, state.2)
  | .addSigned => Addition.TTK.overflowOutput state
  | .subtractSigned => Addition.TTK.overflowSubtractionOutput state

/-- Every actual focused gate list implements the existing exact arithmetic specification. -/
theorem focusGates_step (length : Nat) (operation : Operation)
    (state : Addition.TTK.OverflowRegisters length) :
    GateSpec.stepList (focusGates length operation) state = focusStep operation state := by
  cases operation with
  | addLow =>
      rw [focusGates, Addition.TTK.ttkWithOverflowGateList_step, Addition.TTK.ttkLowRipple_step]
      rfl
  | subtractLow =>
      rw [focusGates, Addition.TTK.ttkWithOverflowGateList_step, Addition.TTK.ttkSubtraction_step]
      rfl
  | addSigned => exact Addition.TTK.ttkOverflow_step length state
  | subtractSigned => exact Addition.TTK.ttkOverflowSubtraction_step length state

/-- All four operations retain the complete arbitrary source operand. -/
theorem focusStep_source {length : Nat} (operation : Operation)
    (state : Addition.TTK.OverflowRegisters length) :
    (focusStep operation state).1.1 = state.1.1 := by
  cases operation <;> rfl

/-- Lift one actual TTK operand or Sign lens beside the entire retained complement. -/
def liftBit {width : Nat} (window : Window width)
    (bit : EncodedBit (Addition.TTK.overflowEncoding window.length)) :
    EncodedBit (groupedEncoding window) :=
  BinaryLabelEncoding.prodLeftBit _ _ bit

private theorem liftBit_ne {width : Nat} (window : Window width)
    (left right : EncodedBit (Addition.TTK.overflowEncoding window.length))
    (different : left.wire ≠ right.wire) :
    (liftBit window left).wire ≠ (liftBit window right).wire := by
  intro same
  apply different
  exact Fin.ext
    (congrArg (fun index : Fin (groupedEncoding window).width => index.val) same)

/-- Lift each actual native primitive without changing its kind or introducing a new gate. -/
def liftGate {width : Nat} (window : Window width) :
    GateSpec (Addition.TTK.overflowEncoding window.length) → GateSpec (groupedEncoding window)
  | .x target => .x (liftBit window target)
  | .cnot control target different =>
      .cnot (liftBit window control) (liftBit window target) (liftBit_ne window _ _ different)
  | .toffoli first second target controls left right =>
      .toffoli (liftBit window first) (liftBit window second) (liftBit window target)
        (liftBit_ne window _ _ controls) (liftBit_ne window _ _ left) (liftBit_ne window _ _ right)

/-- One lifted actual primitive performs its original action and retains every complementary bit. -/
theorem liftGate_step {width : Nat} (window : Window width)
    (gate : GateSpec (Addition.TTK.overflowEncoding window.length))
    (state : Addition.TTK.OverflowRegisters window.length × Complement window) :
    (liftGate window gate).step state = (gate.step state.1, state.2) := by
  cases gate with
  | x target => rfl
  | cnot control target different =>
      change (if control.get state.1 then (target.flip state.1, state.2) else state) = _
      cases selected : control.get state.1 <;>
        simp [GateSpec.step, EncodedBit.cnotStep, selected]
  | toffoli first second target controls left right =>
      change (if first.get state.1 && second.get state.1 then
        (target.flip state.1, state.2) else state) = _
      cases selected : first.get state.1 && second.get state.1 <;>
        simp [GateSpec.step, EncodedBit.toffoliStep, selected]

private theorem liftList_step {width : Nat} (window : Window width)
    (indices : List (GateSpec (Addition.TTK.overflowEncoding window.length)))
    (state : Addition.TTK.OverflowRegisters window.length × Complement window) :
    GateSpec.stepList (indices.map (liftGate window)) state =
      (GateSpec.stepList indices state.1, state.2) := by
  induction indices generalizing state with
  | nil => rfl
  | cons gate rest ih =>
      simp only [List.map_cons, GateSpec.stepList]
      rw [liftGate_step, ih]

/-- The complete actual TTK primitive list on the full grouped carrier. -/
def gates {width : Nat} (window : Window width) (operation : Operation) :
    List (GateSpec (groupedEncoding window)) :=
  (focusGates window.length operation).map (liftGate window)

/-- The exact whole-group result keeps every complementary field, without a clean-input premise. -/
theorem gates_step {width : Nat} (window : Window width) (operation : Operation)
    (state : Addition.TTK.OverflowRegisters window.length × Complement window) :
    GateSpec.stepList (gates window operation) state = (focusStep operation state.1, state.2) := by
  rw [gates, liftList_step, focusGates_step]

/-- Compile and place the same actual native list on the original source frame. -/
def program {width : Nat} (window : Window width) (operation : Operation) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  ArithmeticWindowPlacement.place window (GateSpec.programList (gates window operation))
    (GateSpec.programList_physical_idx_subset_range _)

/-- Reassemble the exact low or signed arithmetic output and every original outside bit. -/
def step {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) : Registers width :=
  ArithmeticWindowPlacement.placedStep window
    (fun pair => (focusStep operation pair.1, pair.2)) state

/-- Actual elementary execution realizes the exact whole-frame arithmetic on every input label. -/
theorem program_realizes {width : Nat} (window : Window width) (operation : Operation) :
    UnitaryCircuit.Realizes (encoding width) (program window operation)
      (step window operation) := by
  have body : UnitaryCircuit.Realizes (groupedEncoding window)
      (GateSpec.programList (gates window operation))
      (fun pair : Addition.TTK.OverflowRegisters window.length × Complement window =>
        (focusStep operation pair.1, pair.2)) :=
    GateSpec.realizesList_congrStep (gates window operation) (gates_step window operation)
  exact ArithmeticWindowPlacement.place_realizes window
    (body := GateSpec.programList (gates window operation))
    (action := fun pair : Addition.TTK.OverflowRegisters window.length × Complement window =>
      (focusStep operation pair.1, pair.2))
    (GateSpec.programList_physical_idx_subset_range (gates window operation)) body

/-- Exact output grouping exhibits the arithmetic result and all retained fields. -/
theorem step_grouping {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    grouping window (step window operation state) =
      (focusStep operation (grouping window state).1, (grouping window state).2) :=
  (grouping window).apply_symm_apply _

/-- The existing full frame remains live; no window operation allocates a quantum helper. -/
theorem program_physical {width : Nat} (window : Window width) (operation : Operation) :
    (program window operation).physical_idx = List.range (encoding width).width :=
  ArithmeticWindowPlacement.place_physical window _ _

private theorem liftGate_event {width : Nat} (window : Window width)
    (gate : GateSpec (Addition.TTK.overflowEncoding window.length)) :
    (liftGate window gate).event = gate.event := by
  cases gate <;> rfl

/-- The actual native trace is precisely the chosen existing TTK primitive list. -/
theorem program_eventTrace {width : Nat} (window : Window width) (operation : Operation) :
    (program window operation).eventTrace =
      (focusGates window.length operation).map GateSpec.event := by
  rw [program, ArithmeticWindowPlacement.place_eventTrace, GateSpec.programList_eventTrace]
  simp only [gates, List.map_map, Function.comp_def, liftGate_event]

/-- Unit depth counts the same real primitive list with its actual execution order. -/
theorem program_unitDepth {width : Nat} (window : Window width) (operation : Operation) :
    (program window operation).evaluatedEventDepth (fun _ => 1) =
      (focusGates window.length operation).length := by
  rw [program, ArithmeticWindowPlacement.place_evaluatedEventDepth,
    GateSpec.programList_evaluatedEventDepth_unit, gates, List.length_map]

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowProgram
