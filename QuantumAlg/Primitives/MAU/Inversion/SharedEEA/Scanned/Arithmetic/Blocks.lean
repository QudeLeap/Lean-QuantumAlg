/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Guard.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Guard.Original
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Guard.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Guard.Original
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Blocks

/-!
# Both complete native arithmetic blocks in their original source order

The actual scanned remainder block executes signed subtraction, the
paid original Sign complement, then low addback. The coefficient block
executes low subtraction, the paid Sign complement, then signed addition.
Every instruction restores its entire existing pool before the next one.
The original Ctrl-zero premise is retained; original Iter is arbitrary
[LYL+26, sec_EEA/sub_opt.tex:43-48,61-66].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticBlocks

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Emit the original three native remainder Sign gates beside the entire existing pool. -/
def remainderSignProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (poolEncoding width).width (ArithmeticSign.remainderProgram width)

/-- Emit the original native coefficient Sign CNOT beside the same existing physical pool. -/
def coefficientSignProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (poolEncoding width).width (ArithmeticSign.coefficientProgram width)

private lemma remainderSignProgram_realizes (width : Nat)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (remainderSignProgram width) environment
      (ArithmeticAddress.liftSource width ArithmeticSign.remainderStep) :=
  (ArithmeticSign.remainderProgram_realizes (environment := environment) width).onBinaryPrefix

private lemma coefficientSignProgram_realizes (width : Nat)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (coefficientSignProgram width) environment
      (ArithmeticAddress.liftSource width ArithmeticSign.coefficientStep) :=
  (ArithmeticSign.coefficientProgram_realizes (environment := environment) width).onBinaryPrefix

/-- All original remainder instructions and their complete cleanup execute in source order. -/
def remainderProgram (width : Nat) (positive : 1 ≤ width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (RemainderGuard.program width positive true).seq
    ((remainderSignProgram width).seq (RemainderGuard.program width positive false))

/-- All original coefficient instructions and their complete cleanup execute in source order. -/
def coefficientProgram (width : Nat) (positive : 1 ≤ width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (CoefficientGuard.program width positive false).seq
    ((coefficientSignProgram width).seq (CoefficientGuard.program width positive true))

/-- Exact complete original remainder block, returning every shared physical bit unchanged. -/
lemma remainderProgram_apply_source (width : Nat) (positive : 1 ≤ width)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (addressZero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (control : state.1.control = false) :
    (remainderProgram width positive).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode
          (SharedEEA.ArithmeticBlocks.remainderSource state.1, state.2))) := by
  let first := ArithmeticAddress.liftSource width
    (ArithmeticInstruction.sourceStep .remainderSubtract) state
  let second := ArithmeticAddress.liftSource width ArithmeticSign.remainderStep first
  have firstControl : first.1.control = false :=
    SharedEEA.ArithmeticBlocks.source_control width .remainderSubtract state.1 control
  have secondControl : second.1.control = false :=
    (ArithmeticSign.remainderStep_control first.1).trans firstControl
  have firstActual := RemainderGuard.program_apply_encoded_ket width positive true environment
    state clean zero addressZero control
  rw [RemainderGuard.step_eq_original] at firstActual
  simp only [RemainderGuard.instruction, if_true] at firstActual
  have middleActual := (remainderSignProgram_realizes width environment).apply_encoded_ket first
  have lastActual := RemainderGuard.program_apply_encoded_ket width positive false environment
    second clean zero addressZero secondControl
  rw [RemainderGuard.step_eq_original] at lastActual
  simp only [RemainderGuard.instruction, Bool.false_eq_true, if_false] at lastActual
  rw [remainderProgram, UnitaryCircuit.applyNormalized_seq, firstActual,
    UnitaryCircuit.applyNormalized_seq, middleActual, lastActual]
  rfl

/-- Exact complete original coefficient block, returning the same entire physical shared pool. -/
lemma coefficientProgram_apply_source (width : Nat) (positive : 1 ≤ width)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (addressZero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (control : state.1.control = false) :
    (coefficientProgram width positive).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode
          (SharedEEA.ArithmeticBlocks.coefficientSource state.1, state.2))) := by
  let first := ArithmeticAddress.liftSource width
    (ArithmeticInstruction.sourceStep .coefficientSubtract) state
  let second := ArithmeticAddress.liftSource width ArithmeticSign.coefficientStep first
  have firstControl : first.1.control = false :=
    SharedEEA.ArithmeticBlocks.source_control width .coefficientSubtract state.1 control
  have secondControl : second.1.control = false :=
    (ArithmeticSign.coefficientStep_control first.1).trans firstControl
  have firstActual := CoefficientGuard.program_apply_encoded_ket width positive false environment
    state clean zero addressZero control
  rw [CoefficientGuard.step_eq_original] at firstActual
  simp only [CoefficientGuard.instruction, Bool.false_eq_true, if_false] at firstActual
  have middleActual := (coefficientSignProgram_realizes width environment).apply_encoded_ket first
  have lastActual := CoefficientGuard.program_apply_encoded_ket width positive true environment
    second clean zero addressZero secondControl
  rw [CoefficientGuard.step_eq_original] at lastActual
  simp only [CoefficientGuard.instruction, if_true] at lastActual
  rw [coefficientProgram, UnitaryCircuit.applyNormalized_seq, firstActual,
    UnitaryCircuit.applyNormalized_seq, middleActual, lastActual]
  rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticBlocks
