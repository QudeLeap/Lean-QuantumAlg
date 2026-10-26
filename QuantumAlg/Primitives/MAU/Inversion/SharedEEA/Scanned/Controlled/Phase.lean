/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Predicated
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Control
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ZeroShiftControl

/-! # Actual externally fused original ordered phase and complete-clock-zero updates -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledPhaseUpdates

noncomputable section

open EncodedBit

private def prepare (width : Nat) (enough : 2 ≤ width.size) (zero : Bool) :
    List (GateSpec (SharedEEA.encoding width)) :=
  if zero then TerminalPredicate.gates width enough else NativeControl.conditionGates width enough

private def middle (width : Nat) (zero : Bool) : List (GateSpec (SharedEEA.encoding width)) :=
  if zero then PhaseGates.complementGates width else PhaseGates.updateGates width

private def sourceStep (width : Nat) (zero : Bool) : Registers width → Registers width :=
  if zero then ZeroShiftControl.step else NativeControl.step

private lemma original_step (width : Nat) (enough : 2 ≤ width.size) (zero : Bool)
    (state : Registers width) :
    GateSpec.stepList (prepare width enough zero ++ middle width zero ++
      (prepare width enough zero).reverse) state = sourceStep width zero state := by
  cases zero
  · exact NativeControl.gates_step width enough state
  · exact ZeroShiftControl.gates_step width enough state

/-- Complete original predicate computations remain, with only the actual payloads selected. -/
def program (width : Nat) (enough : 2 ≤ width.size) (zero : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledFrame.encoding width).width).toQuantum :=
  ControlledPredicated.program width (prepare width enough zero) (middle width zero)

def step (width : Nat) (zero : Bool) (state : ControlledFrame.Data width) :
    ControlledFrame.Data width :=
  ((if state.2.1 then sourceStep width zero state.1.1 else state.1.1, state.1.2), state.2)

/-- Every original source label, including arbitrary Ctrl/Iter, has exact native selected action. -/
lemma program_realizes (width : Nat) (enough : 2 ≤ width.size) (zero : Bool)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (ControlledFrame.encoding width) (program width enough zero)
      environment (step width zero) := by
  apply (ControlledPredicated.program_realizes width
    (prepare width enough zero) (middle width zero) environment).congrStep
  intro state
  rw [ControlledPredicated.step, original_step]
  rfl

lemma step_disabled (width : Nat) (zero : Bool) (state : ControlledFrame.Data width)
    (disabled : state.2.1 = false) : step width zero state = state := by
  rw [step, disabled]
  rfl

lemma step_pool (width : Nat) (zero : Bool) (state : ControlledFrame.Data width) :
    (step width zero state).1.2 = state.1.2 := rfl

lemma step_external (width : Nat) (zero : Bool) (state : ControlledFrame.Data width) :
    (step width zero state).2 = state.2 := rfl

lemma step_control (width : Nat) (zero : Bool) (state : ControlledFrame.Data width) :
    (step width zero state).1.1.control = state.1.1.control := by
  unfold step
  cases zero <;> split <;> rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledPhaseUpdates
