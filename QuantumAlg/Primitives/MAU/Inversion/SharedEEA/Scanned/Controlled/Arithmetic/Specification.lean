/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.SourceWord
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Guard.Original
import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Guard.Original
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Blocks

/-! # Original mathematical selected arithmetic and the actual Sign word -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledArithmeticBlocks

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private def instruction (signed coefficient : Bool) : ArithmeticInstruction.Instruction :=
  if coefficient then CoefficientGuard.instruction signed else RemainderGuard.instruction signed

private def instructionStep (width : Nat) (signed coefficient : Bool)
    (state : ControlledFrame.Data width) : ControlledFrame.Data width :=
  ((if state.2.1 then ArithmeticInstruction.sourceStep (instruction signed coefficient) state.1.1
    else state.1.1, state.1.2), state.2)

private lemma instruction_control (width : Nat) (signed coefficient : Bool)
    (state : ControlledFrame.Data width) (control : state.1.1.control = false) :
    (instructionStep width signed coefficient state).1.1.control = false := by
  unfold instructionStep
  split
  · exact SharedEEA.ArithmeticBlocks.source_control
      width (instruction signed coefficient) state.1.1 control
  · exact control

private def signGates (width : Nat) (coefficient : Bool) :
    List (GateSpec (SharedEEA.encoding width)) :=
  if coefficient then ArithmeticSign.coefficientGates width else ArithmeticSign.remainderGates width

private def signSource (width : Nat) (coefficient : Bool) : Registers width → Registers width :=
  if coefficient then ArithmeticSign.coefficientStep else ArithmeticSign.remainderStep

private lemma signGates_step (width : Nat) (coefficient : Bool) (state : Registers width) :
    GateSpec.stepList (signGates width coefficient) state = signSource width coefficient state := by
  cases coefficient
  · exact ArithmeticSign.remainderGates_step width state
  · exact ArithmeticSign.coefficientGates_step width state

private def signStep (width : Nat) (coefficient : Bool) (state : ControlledFrame.Data width) :
    ControlledFrame.Data width :=
  ((if state.2.1 then signSource width coefficient state.1.1 else state.1.1, state.1.2), state.2)

private lemma signProgram_realizes (width : Nat) (coefficient : Bool)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (ControlledFrame.encoding width)
      (ControlledSourceWord.program width (signGates width coefficient)) environment
      (signStep width coefficient) := by
  apply (ControlledSourceWord.program_realizes width (signGates width coefficient)
    environment).congrStep
  intro state
  rw [signGates_step]
  rfl

private lemma sign_control (width : Nat) (coefficient : Bool)
    (state : ControlledFrame.Data width) :
    (signStep width coefficient state).1.1.control = state.1.1.control := by
  unfold signStep
  split
  · cases coefficient <;> rfl
  · rfl

private def sourceStep (width : Nat) (coefficient : Bool) : Registers width → Registers width :=
  if coefficient then SharedEEA.ArithmeticBlocks.coefficientSource
  else SharedEEA.ArithmeticBlocks.remainderSource

def step (width : Nat) (coefficient : Bool) (state : ControlledFrame.Data width) :
    ControlledFrame.Data width :=
  ((if state.2.1 then sourceStep width coefficient state.1.1 else state.1.1, state.1.2), state.2)

private lemma complete_steps (width : Nat) (coefficient : Bool)
    (state : ControlledFrame.Data width) :
    instructionStep width coefficient coefficient
      (signStep width coefficient (instructionStep width (!coefficient) coefficient state)) =
      step width coefficient state := by
  cases coefficient <;> cases selected : state.2.1 <;>
    simp only [instructionStep, instruction, signStep, signSource, step, sourceStep,
      selected, Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.not_true,
      RemainderGuard.instruction, CoefficientGuard.instruction,
      SharedEEA.ArithmeticBlocks.remainderSource, SharedEEA.ArithmeticBlocks.coefficientSource]

lemma step_disabled (width : Nat) (coefficient : Bool) (state : ControlledFrame.Data width)
    (disabled : state.2.1 = false) : step width coefficient state = state := by
  rw [step, disabled]
  rfl

lemma step_pool (width : Nat) (coefficient : Bool) (state : ControlledFrame.Data width) :
    (step width coefficient state).1.2 = state.1.2 := rfl

lemma step_external (width : Nat) (coefficient : Bool) (state : ControlledFrame.Data width) :
    (step width coefficient state).2 = state.2 := rfl

lemma step_control (width : Nat) (coefficient : Bool) (state : ControlledFrame.Data width)
    (control : state.1.1.control = false) : (step width coefficient state).1.1.control = false := by
  rw [← complete_steps]
  exact instruction_control width coefficient coefficient _
    ((sign_control width coefficient _).trans
      (instruction_control width (!coefficient) coefficient state control))

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledArithmeticBlocks
