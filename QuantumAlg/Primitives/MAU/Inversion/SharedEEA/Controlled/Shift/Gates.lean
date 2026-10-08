/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Controlled.Shift
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ExtendedClock.Increment.Gates
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Trace

/-!
# Literal controlled word shifts and complete-clock instructions

The original word sweeps and borrowed-work HRS increment are placed on the
original Ctrl wire. Decrement reverses those same self-inverse instructions.
Every complete input frame is admitted, including arbitrary work and Ctrl.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ControlledShift

noncomputable section

open EncodedBit GateSpec NumberTheory.SharedEEA

private def placeGates (width : Nat) (instructions : List (GateSpec (encoding width))) :
    List (GateSpec (encoding width)) :=
  instructions.map (ControlPlacement.placement width).placeGate

private theorem placed_step (width : Nat) (instructions : List (GateSpec (encoding width)))
    (state : Registers width) :
    stepList (placeGates width instructions) state =
      ControlPlacement.placedStep (stepList instructions) state := by
  rw [placeGates, EncodedBit.FullPlacement.placeGates_step]
  simp only [EncodedBit.FullPlacement.step, ControlPlacement.placement_grouping_eq,
    ControlPlacement.fieldEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
    ControlPlacement.placedStep]

private theorem placed_trace (width : Nat) (instructions : List (GateSpec (encoding width))) :
    (placeGates width instructions).map (event .empty) = instructions.map (event .empty) := by
  simp only [placeGates, List.map_map, Function.comp_def,
    EncodedBit.FullPlacement.placeGate_event]

/-- The existing-clock increment's actual instruction word at Ctrl's original wire. -/
def incrementGates (width : Nat) : List (GateSpec (encoding width)) :=
  placeGates width (ExtendedClockIncrement.gates width)

private theorem incrementGates_step (width : Nat) (state : Registers width) :
    stepList (incrementGates width) state = counterStep PaddingClock.increment state := by
  rw [incrementGates, placed_step]
  unfold ControlPlacement.placedStep
  rw [ExtendedClockIncrement.extendedClockIncrement_gates_step]
  exact exchanged_counter width PaddingClock.increment state

private theorem decrementGates_step (width : Nat) (state : Registers width) :
    stepList (incrementGates width).reverse state = counterStep PaddingClock.decrement state := by
  have inverse : counterStep PaddingClock.increment (counterStep PaddingClock.decrement state) =
      state := by
    rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
      ⟨p1, p2, sign, iter⟩, control⟩
    cases control with
    | false => rfl
    | true =>
        simp only [counterStep, if_true]
        exact congrArg
          (fun pair : BitVec (width + 3) × BitVec width.size =>
            Registers.mk pair.1 word2 lengthT lengthQ lengthR pair.2 ⟨p1, p2, sign, iter⟩ true)
          (PaddingClock.increment_decrement (word1, shift))
  have restored := stepList_reverse_stepList (incrementGates width)
    (counterStep PaddingClock.decrement state)
  rw [incrementGates_step, inverse] at restored
  exact restored

/-- Original left word sweep followed by every actual borrowed-work increment instruction. -/
def leftGates (width : Nat) : List (GateSpec (encoding width)) :=
  placeGates width (Work2PhaseRotation.leftGates width) ++ incrementGates width

/-- Original right word sweep followed by the literal reverse increment instruction word. -/
def rightGates (width : Nat) : List (GateSpec (encoding width)) :=
  placeGates width (Work2PhaseRotation.rightGates width) ++ (incrementGates width).reverse

/-- The actual left word preserves the exact full state action and arbitrary work restoration. -/
theorem controlledShift_leftGates_step (width : Nat) (state : Registers width) :
    stepList (leftGates width) state = leftStep state := by
  rw [leftGates, stepList_append, placed_step, incrementGates_step]
  have word : ControlPlacement.placedStep
      (stepList (Work2PhaseRotation.leftGates width)) state =
        wordStep (fun word => word.rotateLeft 1) state := by
    unfold ControlPlacement.placedStep
    rw [Work2PhaseRotation.left_step]
    exact exchanged_word width (fun word => word.rotateLeft 1) state
  rw [word]
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iter⟩, control⟩
  cases control <;> rfl

/-- Literal reverse HRS instructions realize decrement on every finite-clock value. -/
theorem controlledShift_rightGates_step (width : Nat) (state : Registers width) :
    stepList (rightGates width) state = rightStep state := by
  rw [rightGates, stepList_append, placed_step, decrementGates_step]
  have word : ControlPlacement.placedStep
      (stepList (Work2PhaseRotation.rightGates width)) state =
        wordStep (fun word => word.rotateRight 1) state := by
    unfold ControlPlacement.placedStep
    rw [Work2PhaseRotation.right_step]
    exact exchanged_word width (fun word => word.rotateRight 1) state
  rw [word]
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iter⟩, control⟩
  cases control <;> rfl

/-- Exact amplitude realization of the placed native left shift at any supplied layout. -/
theorem controlledShift_leftGates_realizes (width : Nat)
    (layout : QubitLayout (encoding width).width) :
    UnitaryCircuit.Realizes (layout := layout) (encoding width)
      (programList layout .empty (leftGates width)) leftStep :=
  realizesList_congrStep layout .empty _ (controlledShift_leftGates_step width)

/-- Exact amplitude realization of the placed native right shift, with no work premise. -/
theorem controlledShift_rightGates_realizes (width : Nat)
    (layout : QubitLayout (encoding width).width) :
    UnitaryCircuit.Realizes (layout := layout) (encoding width)
      (programList layout .empty (rightGates width)) rightStep :=
  realizesList_congrStep layout .empty _ (controlledShift_rightGates_step width)

private theorem incrementGates_trace (width : Nat) :
    (incrementGates width).map (event .empty) = (incrementProgram width).eventTrace := by
  rw [incrementGates, placed_trace, ExtendedClockIncrement.extendedClockIncrement_gates_trace,
    incrementProgram, ControlPlacement.place_eventTrace]

/-- Every left-shift instruction retains its original ordered native event. -/
theorem controlledShift_leftGates_trace (width : Nat) :
    (leftGates width).map (event .empty) = (leftProgram width).eventTrace := by
  rw [leftGates, List.map_append, placed_trace, incrementGates_trace, left_eventTrace,
    incrementProgram, ControlPlacement.place_eventTrace]

/-- The right-shift trace contains the exact reversed native increment trace. -/
theorem controlledShift_rightGates_trace (width : Nat) :
    (rightGates width).map (event .empty) = (rightProgram width).eventTrace := by
  rw [rightGates, List.map_append, placed_trace, List.map_reverse, incrementGates_trace,
    right_eventTrace, AlgorithmGate.oracleFreeAdjoints_eventTrace]

end

end QuantumAlg.MAU.Inversion.SharedEEA.ControlledShift
