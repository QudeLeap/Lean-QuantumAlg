/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Predicate
import all QuantumAlg.Components.Encoded.BitGates.Realization

/-!
# Paid phase-enable preparation in the original EEA control bit

Two actual CNOTs XOR the two retained phase bits into the original Ctrl.
They allocate no system, retain every other source field and the complete
scan pool, and are reversed by the same preparation after the payload.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionEnable

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private lemma first_control (width : Nat) :
    (phase1Bit width).wire ≠ (controlBit width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [phase1Bit_wire, controlBit_wire] at values
  omega

private lemma second_control (width : Nat) :
    (phase2Bit width).wire ≠ (controlBit width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [phase2Bit_wire, controlBit_wire] at values
  omega

/-- Literal original-frame phase CNOTs, each with its full physical support. -/
def sourceGates (width : Nat) : List (GateSpec (SharedEEA.encoding width)) :=
  [.cnot (phase1Bit width) (controlBit width) (first_control width),
    .cnot (phase2Bit width) (controlBit width) (second_control width)]

/-- All original source fields are retained except the actual control XOR. -/
def sourceStep (width : Nat) (state : Registers width) : Registers width :=
  NativePredicate.xorControl (state.flags.first ^^ state.flags.second) state

private lemma source_gates_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (sourceGates width) state = sourceStep width state := by
  rcases state with ⟨word1, word2, coefficient, quotient, divisor, shift,
    ⟨first, second, sign, iteration⟩, control⟩
  cases first <;> cases second <;> cases control <;> rfl

private def sourceProgram (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (SharedEEA.encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (sourceGates width)

private lemma source_realizes (width : Nat) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (SharedEEA.encoding width) (sourceProgram width) environment
      (sourceStep width) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (source_gates_step width) environment

/-- Place those actual CNOTs on the original source prefix and retain the entire pool. -/
def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (poolEncoding width).width (sourceProgram width)

/-- The complete joint source/pool action preserves arbitrary dirty pool contents. -/
def step (width : Nat) (state : Data width) : Data width :=
  (sourceStep width state.1, state.2)

/-- Complete coherent semantics retain the original phase and all surrounding correlations. -/
lemma program_realizes (width : Nat) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width) environment (step width) :=
  (source_realizes width environment).onBinaryPrefix

/-- The same two actual phase CNOTs clear their enable computation on every input label. -/
lemma step_step (width : Nat) (state : Data width) :
    step width (step width state) = state := by
  apply Prod.ext
  · exact NativePredicate.xorControl_twice _ state.1
  · rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionEnable
