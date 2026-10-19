/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout

/-!
# The actual Sign complements between the source arithmetic instructions

After the signed remainder subtraction, the source complements Sign in
phase 2, namely when Phase1 is zero and Phase2 is one
[LYL+26, sec_EEA/sub_opt.tex:43-48]. The coefficient block complements
Sign whenever Phase1 is one, between its conditional low subtraction and
signed addition [LYL+26, sec_EEA/sub_opt.tex:61-66].

These are three actual X/Toffoli/X gates and one actual CNOT respectively.
They use only the already declared phase and Sign wires. Every other bit,
including arbitrary Ctrl and Iter, is retained on every full input label.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticSign

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit

private lemma first_second_ne (width : Nat) :
    (phase1Bit width).wire ≠ (phase2Bit width).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  rw [phase1Bit_wire, phase2Bit_wire] at values
  omega

private lemma first_sign_ne (width : Nat) :
    (phase1Bit width).wire ≠ (signBit width).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  rw [phase1Bit_wire, signBit_wire] at values
  omega

private lemma second_sign_ne (width : Nat) :
    (phase2Bit width).wire ≠ (signBit width).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  rw [phase2Bit_wire, signBit_wire] at values
  omega

/-- Negative Phase1 control is implemented by its actual X mask and its actual inverse. -/
def remainderGates (width : Nat) : List (GateSpec (encoding width)) :=
  [.x (phase1Bit width),
    .toffoli (phase1Bit width) (phase2Bit width) (signBit width)
      (first_second_ne width) (first_sign_ne width) (second_sign_ne width),
    .x (phase1Bit width)]

/-- Complete source remainder Sign update, selected by both actual phase fields. -/
def remainderStep {width : Nat} (state : Registers width) : Registers width :=
  { state with flags := { state.flags with
      sign := state.flags.sign ^^ (!state.flags.first && state.flags.second) } }

/-- The literal native list implements the full phase-selected Sign update on every label. -/
lemma remainderGates_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (remainderGates width) state = remainderStep state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨first, second, sign, iteration⟩, control⟩
  cases first <;> cases second <;> cases sign <;> rfl

/-- The actual coefficient Sign complement is one CNOT from the original Phase1. -/
def coefficientGates (width : Nat) : List (GateSpec (encoding width)) :=
  [.cnot (phase1Bit width) (signBit width) (first_sign_ne width)]

/-- Complete source coefficient Sign update between low subtraction and signed addition. -/
def coefficientStep {width : Nat} (state : Registers width) : Registers width :=
  { state with flags := { state.flags with sign := state.flags.sign ^^ state.flags.first } }

/-- The literal CNOT changes exactly the original Sign and retains every other original bit. -/
lemma coefficientGates_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (coefficientGates width) state = coefficientStep state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨first, second, sign, iteration⟩, control⟩
  cases first <;> cases sign <;> rfl

/-- Compile exactly the remainder Sign mask/Toffoli/inverse-mask list. -/
def remainderProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (remainderGates width)

/-- Compile exactly the coefficient Sign CNOT. -/
def coefficientProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (coefficientGates width)

/-- Exact whole-frame basis amplitudes of the actual remainder Sign program. -/
lemma remainderProgram_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (remainderProgram width) environment remainderStep :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (remainderGates width) (remainderGates_step width) environment

/-- Exact whole-frame basis amplitudes of the actual coefficient Sign program. -/
lemma coefficientProgram_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (coefficientProgram width) environment
      coefficientStep :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (coefficientGates width) (coefficientGates_step width) environment

/-- Remainder Sign changes never alter the original Ctrl. -/
lemma remainderStep_control {width : Nat} (state : Registers width) :
    (remainderStep state).control = state.control := rfl

/-- Coefficient Sign changes never alter the original Ctrl. -/
lemma coefficientStep_control {width : Nat} (state : Registers width) :
    (coefficientStep state).control = state.control := rfl

/-- The actual inverse remainder native list restores every input field. -/
lemma remainderGates_inverse (width : Nat) (state : Registers width) :
    GateSpec.stepList (remainderGates width).reverse (remainderStep state) = state := by
  rw [← remainderGates_step]
  exact GateSpec.stepList_reverse_stepList _ state

/-- The actual inverse coefficient native list restores every input field. -/
lemma coefficientGates_inverse (width : Nat) (state : Registers width) :
    GateSpec.stepList (coefficientGates width).reverse (coefficientStep state) = state := by
  rw [← coefficientGates_step]
  exact GateSpec.stepList_reverse_stepList _ state

/-- Every input emits the actual X/Toffoli/X trace, including inactive phase inputs. -/
lemma remainderProgram_eventTrace (width : Nat) :
    (remainderProgram width).eventTrace =
      [.gate .singleQubit, .gate .toffoli, .gate .singleQubit] := by
  rw [remainderProgram, GateSpec.programList_eventTrace]
  rfl

/-- Every input emits the actual single CNOT event. -/
lemma coefficientProgram_eventTrace (width : Nat) :
    (coefficientProgram width).eventTrace = [.gate .cnot] := by
  rw [coefficientProgram, GateSpec.programList_eventTrace]
  rfl

/-- Actual strict sequential unit depth includes both negative-control mask gates. -/
lemma remainderProgram_unitDepth (width : Nat) :
    (remainderProgram width).evaluatedEventDepth (fun _ => 1) = 3 :=
  GateSpec.programList_evaluatedEventDepth_unit (QubitLayout.canonical _) .empty _

/-- Actual unit depth of the coefficient Sign CNOT. -/
lemma coefficientProgram_unitDepth (width : Nat) :
    (coefficientProgram width).evaluatedEventDepth (fun _ => 1) = 1 :=
  GateSpec.programList_evaluatedEventDepth_unit (QubitLayout.canonical _) .empty _

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticSign
