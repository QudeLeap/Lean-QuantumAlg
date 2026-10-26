/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Parallel.Instruction

/-!
# Direct chronological execution of both complete selected arithmetic blocks

The two actual selected instructions surround the same paid Sign update.
Each intermediate source retains the original pool, external wires and
internal-control condition. The result is the independent original
arithmetic-block source function, with no legacy block executor theorem.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Original mathematical arithmetic block under the same external selection. -/
def arithmeticStep (width : Nat) (coefficient : Bool) (state : ControlledFrame.Data width) :
    ControlledFrame.Data width :=
  ((if state.2.1 then
      (if coefficient then SharedEEA.ArithmeticBlocks.coefficientSource
        else SharedEEA.ArithmeticBlocks.remainderSource) state.1.1
    else state.1.1, state.1.2), state.2)

private lemma complete_steps (width : Nat) (coefficient : Bool)
    (state : ControlledFrame.Data width) :
    instructionStep width coefficient coefficient
      (ControlledArithmeticBlocks.signStep width coefficient
        (instructionStep width (!coefficient) coefficient state)) =
      arithmeticStep width coefficient state :=
  ControlledArithmeticBlocks.complete_steps width coefficient state

/-- Actual instructions and the actual Sign word have their original full mathematical action. -/
lemma arithmeticProgram_apply_encoded_ket (width : Nat) (positive : 1 ≤ width)
    (coefficient : Bool) (environment : OracleModel.empty.Interpretation)
    (state : ControlledFrame.Data width)
    (clean : state.1.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.1.2.2.2 = false)
    (addressZero : state.1.2.1 = 0#(ScanMetadata.addressWidth width))
    (control : state.1.1.control = false) :
    (arithmeticProgram width positive coefficient).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode (arithmeticStep width coefficient state))) := by
  let first := instructionStep width (!coefficient) coefficient state
  let second := ControlledArithmeticBlocks.signStep width coefficient first
  have firstControl : first.1.1.control = false :=
    instructionStep_control width (!coefficient) coefficient state control
  have secondControl : second.1.1.control = false :=
    (ControlledArithmeticBlocks.sign_control width coefficient first).trans firstControl
  have firstActual := instructionProgram_apply_encoded_ket
    width positive (!coefficient) coefficient environment state clean zero addressZero control
  have middleActual :=
    (ControlledArithmeticBlocks.signProgram_realizes width coefficient
      environment).apply_encoded_ket first
  have lastActual := instructionProgram_apply_encoded_ket
    width positive coefficient coefficient environment second clean zero addressZero secondControl
  have actual := UnitaryCircuit.applyNormalized_seq_of_eq firstActual
    (UnitaryCircuit.applyNormalized_seq_of_eq middleActual lastActual)
  change (arithmeticProgram width positive coefficient).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode state))) =
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((ControlledFrame.encoding width).encode
        (instructionStep width coefficient coefficient
          (ControlledArithmeticBlocks.signStep width coefficient
            (instructionStep width (!coefficient) coefficient state))))) at actual
  rw [complete_steps] at actual
  exact actual

lemma arithmeticStep_pool (width : Nat) (coefficient : Bool) (state : ControlledFrame.Data width) :
    (arithmeticStep width coefficient state).1.2 = state.1.2 := rfl

lemma arithmeticStep_external (width : Nat) (coefficient : Bool)
    (state : ControlledFrame.Data width) :
    (arithmeticStep width coefficient state).2 = state.2 := rfl

lemma arithmeticStep_control (width : Nat) (coefficient : Bool)
    (state : ControlledFrame.Data width) (control : state.1.1.control = false) :
    (arithmeticStep width coefficient state).1.1.control = false :=
  ControlledArithmeticBlocks.step_control width coefficient state control

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel
