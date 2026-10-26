/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Native.Support
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Ext
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Frame
import all QuantumAlg.Components.Encoded.BitGates.Dirty.Control

/-!
# Paid coherent phase selection for complete coefficient geometry

Original Phase2 controls literal native X/CNOT/Toffoli words. One
original operand bit is arbitrary borrowed work, restored within every
source primitive. Two real X masks implement the negative phase; no
runtime field is passed to a host circuit-construction callback.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry

noncomputable section

open EncodedBit ArithmeticGuard

private lemma phase_outside (width : Nat) : outsideMetadata width (phase2Bit width) := by
  right
  rw [phase2Bit_wire]
  omega

private lemma work_outside (width : Nat) :
    outsideMetadata width (firstWordBit width ⟨0, by omega⟩) := by
  left
  change 0 < 2 * (width + 3)
  omega

private lemma control_disjoint (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (gate : GateSpec (encoding width))
    (present : gate ∈ nativeCoefficientGates width positive deshift) :
    GateSpec.bitDisjoint (flag width 1) gate :=
  nativeCoefficientGates_bitDisjoint width positive deshift (phase2Bit width)
    (phase_outside width) gate present

private lemma work_disjoint (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (gate : GateSpec (encoding width))
    (present : gate ∈ nativeCoefficientGates width positive deshift) :
    GateSpec.bitDisjoint (work width) gate :=
  nativeCoefficientGates_bitDisjoint width positive deshift _ (work_outside width) gate present

/-- One real positive Phase2 control for either complete fixed native coefficient word. -/
def phaseControlledGates (width : Nat) (positive : 1 ≤ width) (deshift : Bool) :
    List (GateSpec (encoding width)) :=
  GateSpec.listWithDirtyControl (flag width 1) (work width)
    (nativeCoefficientGates width positive deshift) (control_disjoint width positive deshift)
    (work_disjoint width positive deshift) (flag_work_ne width 1)

/-- Original Phase2 selects the entire fixed action and every arbitrary borrowed bit returns. -/
lemma phaseControlledGates_step (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (state : Data width) :
    GateSpec.stepList (phaseControlledGates width positive deshift) state =
      if state.1.flags.second then coefficientStep width positive deshift state else state := by
  rw [phaseControlledGates, GateSpec.listWithDirtyControl_step, nativeCoefficientGates_step]
  rfl

private lemma coefficientStep_phase2_flip (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (state : Data width) :
    coefficientStep width positive deshift ((flag width 1).flip state) =
      (flag width 1).flip (coefficientStep width positive deshift state) := by
  apply data_eq_of_source_prefix_target width
  · change (coefficientStep width positive deshift ((flag width 1).flip state)).1 =
      { (coefficientStep width positive deshift state).1 with
        flags := { (coefficientStep width positive deshift state).1.flags with
          second := !(coefficientStep width positive deshift state).1.flags.second } }
    rw [coefficientStep_source, coefficientStep_source]
    rfl
  · change (coefficientStep width positive deshift ((flag width 1).flip state)).2.2.1 =
      (coefficientStep width positive deshift state).2.2.1
    rw [coefficientStep_prefix, coefficientStep_prefix]
    rfl
  · change targetValue width
      (coefficientStep width positive deshift ((flag width 1).flip state)) =
        targetValue width (coefficientStep width positive deshift state)
    rw [coefficientStep_targetValue, coefficientStep_targetValue]
    cases deshift <;> rfl

/-- Negative and positive actual Phase2 controls both execute as literal native instructions. -/
def runtimeCoefficientGates (width : Nat) (positive : 1 ≤ width) :
    List (GateSpec (encoding width)) :=
  (.x (flag width 1) :: phaseControlledGates width positive false) ++
    (.x (flag width 1) :: phaseControlledGates width positive true)

/-- Independent full finite conditional geometry action on original source registers. -/
def runtimeCoefficientStep (width : Nat) (positive : 1 ≤ width) (state : Data width) : Data width :=
  if state.1.flags.second then coefficientStep width positive true state
  else coefficientStep width positive false state

/-- The full coherent gate word selects the actual source phase without changing Phase2. -/
lemma runtimeCoefficientGates_step (width : Nat) (positive : 1 ≤ width) (state : Data width) :
    GateSpec.stepList (runtimeCoefficientGates width positive) state =
      runtimeCoefficientStep width positive state := by
  rw [runtimeCoefficientGates, GateSpec.stepList_append]
  change GateSpec.stepList (phaseControlledGates width positive true)
    ((flag width 1).flip
      (GateSpec.stepList (phaseControlledGates width positive false)
        ((flag width 1).flip state))) = _
  rw [phaseControlledGates_step width positive false ((flag width 1).flip state)]
  have flipped : ((flag width 1).flip state).1.flags.second = !state.1.flags.second := rfl
  rw [flipped]
  cases selected : state.1.flags.second with
  | false =>
      simp only [Bool.not_false, if_true]
      rw [coefficientStep_phase2_flip, EncodedBit.flip_flip, phaseControlledGates_step]
      have retained := congrArg (fun source : Registers width => source.flags.second)
        (coefficientStep_source width positive false state)
      rw [retained, selected]
      simp only [runtimeCoefficientStep, selected, Bool.false_eq_true, if_false]
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      rw [EncodedBit.flip_flip, phaseControlledGates_step, selected]
      simp only [runtimeCoefficientStep, selected, if_true]

/-- Compile the same paid coherent source-phase selection without allocating any extra qubit. -/
def runtimeCoefficientProgram (width : Nat) (positive : 1 ≤ width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (runtimeCoefficientGates width positive)

/-- All finite labels and arbitrary reference superpositions follow the same actual gate word. -/
lemma runtimeCoefficientProgram_realizes (width : Nat) (positive : 1 ≤ width)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (runtimeCoefficientProgram width positive) environment
      (runtimeCoefficientStep width positive) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (runtimeCoefficientGates_step width positive) environment

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry
