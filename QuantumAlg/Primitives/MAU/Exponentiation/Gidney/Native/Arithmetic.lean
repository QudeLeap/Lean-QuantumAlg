/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Dirty.Control
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive
import all QuantumAlg.Primitives.MAU.Multiplication.DirtyBorrowed

/-!
# Native arithmetic blocks for modular exponentiation

This module starts the polynomial gate-level route used by native modular
exponentiation.  It adds an exponent-bit control to the existing HRS
source-controlled fixed-width adder.  The extra control is lowered to literal
X/CNOT/Toffoli gates, borrowing the otherwise arbitrary comparison coordinate
as dirty work and restoring it for every basis label.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney.NativeArithmetic

noncomputable section

open EncodedBit EncodedBit.GateSpec

open MAU.Multiplication.DirtyBorrowed

/-- One exponent control followed by the two arithmetic words and the
arbitrary comparison coordinate used by the HRS adder layout. -/
abbrev ControlledAdderRegisters (tail : Nat) :=
  Bool × State tail.succ (LiteralBorrowed tail.succ)

/-- Binary layout of the controlled HRS arithmetic checkpoint. -/
def controlledAdderEncoding (tail : Nat) :
    BinaryLabelEncoding (ControlledAdderRegisters tail) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool
    (literalR0Encoding tail.succ)

/-- The added exponent-bit control. -/
def exponentControlBit (tail : Nat) :
    EncodedBit (controlledAdderEncoding tail) :=
  BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
    (literalR0Encoding tail.succ) BinaryLabelEncoding.boolBit

/-- The arbitrary coordinate borrowed while lowering three-control gates. -/
def borrowedControlWorkBit (tail : Nat) :
    EncodedBit (controlledAdderEncoding tail) :=
  BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
    (literalR0Encoding tail.succ) (literalFlagBit tail.succ)

/-- Lift the actual source-controlled HRS adder into the right-hand arithmetic
field without changing its primitive gate list. -/
def liftedSourceControlledAdderGates (tail : Nat) (pivot : Fin tail.succ)
    (constant : PlainAdder.Word tail.succ) :
    List (GateSpec (controlledAdderEncoding tail)) :=
  (sourceControlledAdderGates tail pivot constant).map
    (GateSpec.prodRight BinaryLabelEncoding.bool)

private theorem liftedSourceControlledAdder_controlDisjoint (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ∀ gate, gate ∈ liftedSourceControlledAdderGates tail pivot constant →
      GateSpec.bitDisjoint (exponentControlBit tail) gate := by
  intro gate present
  obtain ⟨sourceGate, _sourcePresent, rfl⟩ := List.mem_map.mp present
  exact GateSpec.bitDisjoint_prodRight_leftBit
    BinaryLabelEncoding.bool (literalR0Encoding tail.succ)
    BinaryLabelEncoding.boolBit sourceGate

private theorem liftedSourceControlledAdder_workDisjoint (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ∀ gate, gate ∈ liftedSourceControlledAdderGates tail pivot constant →
      GateSpec.bitDisjoint (borrowedControlWorkBit tail) gate := by
  intro gate present
  obtain ⟨sourceGate, sourcePresent, rfl⟩ := List.mem_map.mp present
  apply GateSpec.bitDisjoint_prodRight_of_bitDisjoint
  exact List.forall_iff_forall_mem.mp
    (sourceControlledAdderGates_forall_bitDisjoint_flag
      tail pivot constant) sourceGate sourcePresent

private theorem exponentControlBit_wire_ne_borrowedControlWorkBit (tail : Nat) :
    (exponentControlBit tail).wire ≠ (borrowedControlWorkBit tail).wire :=
  (GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    BinaryLabelEncoding.bool (literalR0Encoding tail.succ)
    (literalFlagBit tail.succ) BinaryLabelEncoding.boolBit).symm

/-- Literal X/CNOT/Toffoli implementation of an exponent-bit-controlled,
source-bit-controlled fixed-width addition. -/
def doubleControlledAdderGates (tail : Nat) (pivot : Fin tail.succ)
    (constant : PlainAdder.Word tail.succ) :
    List (GateSpec (controlledAdderEncoding tail)) :=
  GateSpec.listWithDirtyControl
    (exponentControlBit tail) (borrowedControlWorkBit tail)
    (liftedSourceControlledAdderGates tail pivot constant)
    (liftedSourceControlledAdder_controlDisjoint tail pivot constant)
    (liftedSourceControlledAdder_workDisjoint tail pivot constant)
    (exponentControlBit_wire_ne_borrowedControlWorkBit tail)

/-- Independent complete-label action of the doubly controlled adder. -/
def doubleControlledAdd (tail : Nat) (pivot : Fin tail.succ)
    (constant : PlainAdder.Word tail.succ)
    (state : ControlledAdderRegisters tail) : ControlledAdderRegisters tail :=
  if state.1 then
    (state.1, sourceControlledAdd tail pivot constant state.2)
  else
    state

/-- The literal lowering applies the HRS adder exactly when the exponent
control is set; all source and dirty-work coordinates retain their values. -/
theorem doubleControlledAdderGates_step (tail : Nat) (pivot : Fin tail.succ)
    (constant : PlainAdder.Word tail.succ)
    (state : ControlledAdderRegisters tail) :
    GateSpec.stepList (doubleControlledAdderGates tail pivot constant) state =
      doubleControlledAdd tail pivot constant state := by
  rw [doubleControlledAdderGates, GateSpec.listWithDirtyControl_step]
  change (if state.1 then
      GateSpec.stepList (liftedSourceControlledAdderGates tail pivot constant) state
    else state) = _
  by_cases selected : state.1
  · rw [if_pos selected]
    rw [show GateSpec.stepList
        (liftedSourceControlledAdderGates tail pivot constant) state =
        (state.1, sourceControlledAdderStep tail pivot constant state.2) by
      exact GateSpec.stepList_prodRight BinaryLabelEncoding.bool
        (sourceControlledAdderGates tail pivot constant) state]
    rw [sourceControlledAdderStep_eq]
    simp [doubleControlledAdd, selected]
  · rw [if_neg selected]
    simp [doubleControlledAdd, selected]

/-- Canonical circuit compiled from the emitted elementary gate list. -/
def doubleControlledAdderProgram (tail : Nat) (pivot : Fin tail.succ)
    (constant : PlainAdder.Word tail.succ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (controlledAdderEncoding tail).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical (controlledAdderEncoding tail).width)
    .empty (doubleControlledAdderGates tail pivot constant)

/-- The compiled circuit realizes the same independently stated action. -/
theorem doubleControlledAdderProgram_realizes (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    UnitaryCircuit.Realizes (controlledAdderEncoding tail)
      (doubleControlledAdderProgram tail pivot constant)
      (doubleControlledAdd tail pivot constant) :=
  GateSpec.realizesList_congrStep
    (QubitLayout.canonical (controlledAdderEncoding tail).width) .empty
    (doubleControlledAdderGates tail pivot constant)
    (doubleControlledAdderGates_step tail pivot constant)

/-- The emitted list has the exact dirty-control expansion length of its
source HRS gate list. -/
theorem doubleControlledAdderGates_length (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    (doubleControlledAdderGates tail pivot constant).length =
      ((liftedSourceControlledAdderGates tail pivot constant).map
        GateSpec.dirtyControlCount).sum := by
  exact GateSpec.listWithDirtyControl_length
    (exponentControlBit tail) (borrowedControlWorkBit tail)
    (liftedSourceControlledAdderGates tail pivot constant)
    (liftedSourceControlledAdder_controlDisjoint tail pivot constant)
    (liftedSourceControlledAdder_workDisjoint tail pivot constant)
    (exponentControlBit_wire_ne_borrowedControlWorkBit tail)

private theorem liftedSourceControlledAdderGates_xMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ((liftedSourceControlledAdderGates tail pivot constant).map
      GateSpec.xMultiplicity).sum =
      sourceControlledHighXClosedForm constant tail := by
  apply (GateSpec.sum_xMultiplicity_eq_of_events_eq .empty
    (GateSpec.map_event_prodRight BinaryLabelEncoding.bool
      (sourceControlledAdderGates tail pivot constant))).trans
  exact sourceControlledAdderGates_xMultiplicity_sum tail pivot constant

private theorem liftedSourceControlledAdderGates_cnotMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ((liftedSourceControlledAdderGates tail pivot constant).map
      GateSpec.cnotMultiplicity).sum =
      controlledAdderCnotClosedForm constant tail := by
  apply (GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty
    (GateSpec.map_event_prodRight BinaryLabelEncoding.bool
      (sourceControlledAdderGates tail pivot constant))).trans
  exact sourceControlledAdderGates_cnotMultiplicity_sum tail pivot constant

private theorem liftedSourceControlledAdderGates_toffoliMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ((liftedSourceControlledAdderGates tail pivot constant).map
      GateSpec.toffoliMultiplicity).sum = 2 * tail * tail := by
  apply (GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty
    (GateSpec.map_event_prodRight BinaryLabelEncoding.bool
      (sourceControlledAdderGates tail pivot constant))).trans
  exact sourceControlledAdderGates_toffoliMultiplicity_sum tail pivot constant

/-- Adding the exponent control eliminates physical X instructions: source
X gates become CNOTs and every other source gate becomes a Toffoli network. -/
theorem doubleControlledAdderGates_xMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ((doubleControlledAdderGates tail pivot constant).map
      GateSpec.xMultiplicity).sum = 0 := by
  exact GateSpec.listWithDirtyControl_xMultiplicity_sum
    (exponentControlBit tail) (borrowedControlWorkBit tail)
    (liftedSourceControlledAdderGates tail pivot constant)
    (liftedSourceControlledAdder_controlDisjoint tail pivot constant)
    (liftedSourceControlledAdder_workDisjoint tail pivot constant)
    (exponentControlBit_wire_ne_borrowedControlWorkBit tail)

/-- Exact physical CNOT coordinate of the exponent-controlled actual adder. -/
theorem doubleControlledAdderGates_cnotMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ((doubleControlledAdderGates tail pivot constant).map
      GateSpec.cnotMultiplicity).sum =
      sourceControlledHighXClosedForm constant tail := by
  rw [doubleControlledAdderGates,
    GateSpec.listWithDirtyControl_cnotMultiplicity_sum,
    liftedSourceControlledAdderGates_xMultiplicity_sum]

/-- Exact physical Toffoli coordinate of the exponent-controlled actual
adder, including the four-Toffoli arbitrary-work lowering of every source
Toffoli. -/
theorem doubleControlledAdderGates_toffoliMultiplicity_sum (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ((doubleControlledAdderGates tail pivot constant).map
      GateSpec.toffoliMultiplicity).sum =
      controlledAdderCnotClosedForm constant tail + 8 * tail * tail := by
  rw [doubleControlledAdderGates,
    GateSpec.listWithDirtyControl_toffoliMultiplicity_sum,
    liftedSourceControlledAdderGates_cnotMultiplicity_sum,
    liftedSourceControlledAdderGates_toffoliMultiplicity_sum]
  ring

/-- The compiled program exposes the same exact three-class native counts as
its emitted list. -/
theorem doubleControlledAdderProgram_native_counts (tail : Nat)
    (pivot : Fin tail.succ) (constant : PlainAdder.Word tail.succ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (doubleControlledAdderProgram tail pivot constant).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
          (doubleControlledAdderProgram tail pivot constant).eventCost =
        sourceControlledHighXClosedForm constant tail ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
          (doubleControlledAdderProgram tail pivot constant).eventCost =
        controlledAdderCnotClosedForm constant tail + 8 * tail * tail := by
  constructor
  · rw [doubleControlledAdderProgram, GateSpec.programList_x_count_eq_sum,
      doubleControlledAdderGates_xMultiplicity_sum]
  constructor
  · rw [doubleControlledAdderProgram, GateSpec.programList_cnot_count_eq_sum,
      doubleControlledAdderGates_cnotMultiplicity_sum]
  · rw [doubleControlledAdderProgram, GateSpec.programList_toffoli_count_eq_sum,
      doubleControlledAdderGates_toffoliMultiplicity_sum]

end

end QuantumAlg.MAU.Exponentiation.Gidney.NativeArithmetic
