/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Action
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.SourceWord
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ClockDecode.Gates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Output.Correction.Gates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.InPlace

/-!
# Actual selected full-clock decoding, output correction and same-port unloading

All original binary-weighted decoder repetitions remain in the emitted
word. External lowering is applied to their actual gates, with no free
rotation or omitted retained-clock work. Semantic proofs consume whole
generic words and never evaluate the list at a fixed large width.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCompletion

noncomputable section

open EncodedBit NumberTheory.SharedEEA

def gates (modulus : Nat) : List (GateSpec (SharedEEA.encoding modulus.size)) :=
  ClockDecode.gates modulus.size ++ OutputCorrection.gates modulus

def sourceStep (modulus : Nat) (state : Registers modulus.size) : Registers modulus.size :=
  OutputCorrection.step modulus
    { state with
      secondWord := state.secondWord.rotateRight (ExtendedClockRegisters.clock state).toNat }

/-- Full original decoding and reflection execute before the separate actual output-port word. -/
def program (modulus : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledFrame.encoding modulus.size).width).toQuantum :=
  ControlledSourceWord.program modulus.size (gates modulus)

/-- All-label semantics retain the complete original clock/history, pool and external work. -/
lemma program_realizes (modulus : Nat) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (ControlledFrame.encoding modulus.size) (program modulus) environment
      (ControlledSource.step modulus.size (sourceStep modulus)) := by
  apply (ControlledSourceWord.program_realizes modulus.size (gates modulus) environment).congrStep
  intro state
  rw [gates, GateSpec.stepList_append, ClockDecode.clockDecode_gates_step,
    OutputCorrection.outputCorrection_gates_step]
  rfl

private lemma sourceStep_terminal (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    sourceStep modulus
      (TerminalPosition.frame
        (SharedEEA.NativeSchedule.terminalFrame modulus input positive bounded)
        (QuotientSchedule.padding modulus input)) =
      SharedEEA.CorrectedSchedule.result modulus input positive bounded := by
  rw [sourceStep, TerminalPosition.decode_word
    (SharedEEA.NativeSchedule.terminalFrame modulus input positive bounded)
    (QuotientSchedule.padding modulus input)
    (SharedEEA.NativeSchedule.padding_fits modulus input coprime positive bounded)]
  rfl

/-- Active terminal decoding has the exact original corrected source endpoint. -/
lemma program_terminal_active (modulus input : Nat)
    (environment : OracleModel.empty.Interpretation) (pool : Pool modulus.size)
    (flags : Bool × Bool) (selected : flags.1 = true) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    (program modulus).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding modulus.size).encode
            ((TerminalPosition.frame
              (SharedEEA.NativeSchedule.terminalFrame modulus input positive bounded)
              (QuotientSchedule.padding modulus input), pool), flags)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding modulus.size).encode
          ((SharedEEA.CorrectedSchedule.result modulus input positive bounded, pool),
            flags))) := by
  have actual := (program_realizes modulus environment).apply_encoded_ket
    ((TerminalPosition.frame
      (SharedEEA.NativeSchedule.terminalFrame modulus input positive bounded)
      (QuotientSchedule.padding modulus input), pool), flags)
  simpa only [ControlledSource.step, selected, ↓reduceIte,
    sourceStep_terminal modulus input coprime positive bounded] using actual

/-- The original physical reversal and fixed constant unload receive actual external control. -/
def unloadProgram (modulus : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledFrame.encoding modulus.size).width).toQuantum :=
  ControlledSourceWord.program modulus.size (OutputPortProgram.gates modulus)

/-- Arbitrary source and work labels have the exact selected same-port output action. -/
lemma unloadProgram_realizes (modulus : Nat) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (ControlledFrame.encoding modulus.size) (unloadProgram modulus)
      environment (ControlledSource.step modulus.size (OutputPortProgram.step modulus)) := by
  apply (ControlledSourceWord.program_realizes modulus.size (OutputPortProgram.gates modulus)
    environment).congrStep
  intro state
  rw [OutputPortProgram.gates_step]
  rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCompletion
