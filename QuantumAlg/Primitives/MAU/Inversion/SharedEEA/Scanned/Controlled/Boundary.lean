/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Boundary.Body
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.SourceWord

/-!
# Complete externally selected terminal boundary on the original full frame

Only the original boundary predicates acquire external control. The
original word exchanges, four length writes and Iter update remain the
same actual full body. Both predicate directions execute on their actual
current input, so the last toggle is retained even on unreachable labels.
No nonzero-input or extra finite-clock restriction is imposed on an
inactive external branch.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledBoundary

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private def predicateGates (width : Nat) (enough : 2 ≤ width.size) (inverse : Bool) :
    List (GateSpec (SharedEEA.encoding width)) :=
  if inverse then (BoundaryPredicate.gates width enough).reverse
  else BoundaryPredicate.gates width enough

private lemma predicateGates_step (width : Nat) (enough : 2 ≤ width.size) (inverse : Bool)
    (state : Registers width) :
    GateSpec.stepList (predicateGates width enough inverse) state =
      NativePredicate.xorControl (BoundaryPredicate.condition state) state := by
  cases inverse
  · exact BoundaryPredicate.gates_step width enough state
  · exact BoundaryPredicate.reverse_step width enough state

private def predicateProgram (width : Nat) (enough : 2 ≤ width.size) (inverse : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledFrame.encoding width).width).toQuantum :=
  ControlledSourceWord.program width (predicateGates width enough inverse)

private def predicateStep (width : Nat) (state : ControlledFrame.Data width) :
    ControlledFrame.Data width :=
  ((if state.2.1 then
      NativePredicate.xorControl (BoundaryPredicate.condition state.1.1) state.1.1
    else state.1.1, state.1.2), state.2)

private lemma predicateProgram_realizes (width : Nat) (enough : 2 ≤ width.size)
    (inverse : Bool) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (ControlledFrame.encoding width)
      (predicateProgram width enough inverse) environment (predicateStep width) := by
  apply (ControlledSourceWord.program_realizes width
    (predicateGates width enough inverse) environment).congrStep
  intro state
  rw [predicateGates_step]
  rfl

/-- The complete original body executes between the two actual selected predicate directions. -/
def program (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledFrame.encoding width).width).toQuantum :=
  (predicateProgram width enough false).seq
    ((UnitaryCircuit.onBinaryPrefix ExternalWord.flags.width
      (ControlledBoundaryBody.program width enough)).seq (predicateProgram width enough true))

def step (width : Nat) (state : ControlledFrame.Data width) : ControlledFrame.Data width :=
  ((if state.2.1 then SharedEEA.TerminalBoundary.step state.1.1 else state.1.1,
    state.1.2), state.2)

private lemma complete_steps (width : Nat) (state : ControlledFrame.Data width)
    (control : state.1.1.control = false) :
    predicateStep width
      ((SharedEEA.TerminalBoundary.body (predicateStep width state).1.1,
        (predicateStep width state).1.2), (predicateStep width state).2) = step width state := by
  cases selected : state.2.1 <;>
    simp only [predicateStep, step, selected, Bool.false_eq_true, if_false, if_true,
      SharedEEA.TerminalBoundary.step, ControlledBoundaryBody.source_disabled state.1.1 control]

/-- Full native source semantics return all pool and external work on both external branches. -/
lemma program_apply_encoded_ket (width : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation) (state : ControlledFrame.Data width)
    (prefixZero : state.1.2.2.1 = 0) (addressZero : state.1.2.1 = 0)
    (borrowZero : state.1.2.2.2 = false) (control : state.1.1.control = false) :
    (program width enough).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode (step width state))) := by
  let toggled := predicateStep width state
  let result : ControlledFrame.Data width :=
    ((SharedEEA.TerminalBoundary.body toggled.1.1, toggled.1.2), toggled.2)
  have first :=
    (predicateProgram_realizes width enough false environment).apply_encoded_ket state
  have body := ControlledBoundaryBody.program_apply_encoded_ket width enough environment
    toggled.1 prefixZero addressZero borrowZero
  have middle := UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    (Scanned.encoding width) ExternalWord.flags (ControlledBoundaryBody.program width enough)
    toggled.1 result.1 toggled.2 body
  have last :=
    (predicateProgram_realizes width enough true environment).apply_encoded_ket result
  have actual := UnitaryCircuit.applyNormalized_seq_of_eq first
    (UnitaryCircuit.applyNormalized_seq_of_eq middle last)
  change (program width enough).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode state))) =
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((ControlledFrame.encoding width).encode
        (predicateStep width
          ((SharedEEA.TerminalBoundary.body (predicateStep width state).1.1,
            (predicateStep width state).1.2), (predicateStep width state).2)))) at actual
  rw [complete_steps width state control] at actual
  exact actual

lemma step_disabled (width : Nat) (state : ControlledFrame.Data width)
    (disabled : state.2.1 = false) : step width state = state := by
  rw [step, disabled]
  rfl

lemma step_pool (width : Nat) (state : ControlledFrame.Data width) :
    (step width state).1.2 = state.1.2 := rfl

lemma step_external (width : Nat) (state : ControlledFrame.Data width) :
    (step width state).2 = state.2 := rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledBoundary
