/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Guarded.Shift
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Controlled.Shift.Gates

/-!
# Complete literal native guarded shift

The existing predicate words surround the actual placed shifts and their
finite-clock inverses. Arbitrary incoming Ctrl is restored by the original
predicate cleanup, with no extra initialized workspace.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.GuardedShift

noncomputable section

open EncodedBit GateSpec

/-- Both original predicates, the left pair, two right pairs, and both inverse cleanups. -/
def gates (width : Nat) (selected : Bool) : List (GateSpec (encoding width)) :=
  PhaseGuard.firstGates width selected ++
    ControlledShift.leftGates width ++
    (PhaseGuard.firstGates width selected).reverse ++
    PhaseGuard.descendingGates width selected ++
    ControlledShift.rightGates width ++ ControlledShift.rightGates width ++
    (PhaseGuard.descendingGates width selected).reverse

private theorem firstGates_step (width : Nat) (selected : Bool) (state : Registers width) :
    stepList ((PhaseGuard.firstGates width selected) ++ ControlledShift.leftGates width ++
      (PhaseGuard.firstGates width selected).reverse) state = firstStep selected state := by
  rw [stepList_append, stepList_append, PhaseGuard.first_step,
    ControlledShift.controlledShift_leftGates_step, PhaseGuard.first_reverse_step]
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iter⟩, control⟩
  cases selected <;> cases p1 <;> cases control <;> rfl

private theorem lastGates_step (width : Nat) (selected : Bool) (state : Registers width) :
    stepList ((PhaseGuard.descendingGates width selected) ++ ControlledShift.rightGates width ++
      ControlledShift.rightGates width ++
      (PhaseGuard.descendingGates width selected).reverse) state = lastStep selected state := by
  rw [stepList_append, stepList_append, stepList_append, PhaseGuard.descending_step,
    ControlledShift.controlledShift_rightGates_step,
    ControlledShift.controlledShift_rightGates_step, PhaseGuard.descending_reverse_step]
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iter⟩, control⟩
  cases selected <;> cases p1 <;> cases p2 <;> cases control <;> rfl

/-- Full-frame basis action preserves all dirty data and the original Ctrl cleanup. -/
theorem guardedShift_gates_step (width : Nat) (selected : Bool) (state : Registers width) :
    stepList (gates width selected) state = step selected state := by
  have splitWord : gates width selected =
      ((PhaseGuard.firstGates width selected) ++ ControlledShift.leftGates width ++
        (PhaseGuard.firstGates width selected).reverse) ++
      ((PhaseGuard.descendingGates width selected) ++ ControlledShift.rightGates width ++
        ControlledShift.rightGates width ++
        (PhaseGuard.descendingGates width selected).reverse) := by
    simp only [gates, List.append_assoc]
  rw [splitWord, stepList_append, firstGates_step, lastGates_step]
  rfl

/-- Execute the complete literal native list on the original full register frame. -/
def nativeProgram (width : Nat) (selected : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (gates width selected)

/-- Every amplitude and relative phase agrees with the original guarded source action. -/
theorem guardedShift_nativeProgram_realizes (width : Nat) (selected : Bool) :
    UnitaryCircuit.Realizes (encoding width) (nativeProgram width selected) (step selected) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty _
    (guardedShift_gates_step width selected)

/-- Predicate, shift, inverse and cleanup events retain their exact original ordering. -/
theorem guardedShift_gates_trace (width : Nat) (selected : Bool) :
    (gates width selected).map (event .empty) = (program width selected).eventTrace := by
  simp only [gates, List.map_append, ControlledShift.controlledShift_leftGates_trace,
    ControlledShift.controlledShift_rightGates_trace, program_eventTrace, List.append_assoc]

/-- The consumer's emitted word has exactly the original ordered native trace. -/
theorem guardedShift_nativeProgram_trace (width : Nat) (selected : Bool) :
    (nativeProgram width selected).eventTrace = (program width selected).eventTrace := by
  rw [nativeProgram, programList_eventTrace, guardedShift_gates_trace]

/-- Complete native multiplicities agree with the original actual guarded program. -/
theorem guardedShift_gates_eventCost (width : Nat) (selected : Bool) :
    ResourcePool.ofList ((gates width selected).map (event .empty)) =
      (program width selected).eventCost := by
  rw [guardedShift_gates_trace, UnitaryCircuit.ofList_eventTrace_eq_eventCost]

end

end QuantumAlg.MAU.Inversion.SharedEEA.GuardedShift
