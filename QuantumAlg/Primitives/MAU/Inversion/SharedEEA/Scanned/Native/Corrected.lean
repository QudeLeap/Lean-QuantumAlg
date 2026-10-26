/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.Pruned
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.CorrectedSchedule

/-!
# Actual pruned shared-EEA computation, complete decoder and output correction

The same original decoder and parity correction execute after the new
fixed native cycle. All forward history and the entire pool remain
present. This endpoint identifies the actual corrected word; copying it
and reversing the complete forward computation are separate operations.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CorrectedSchedule

noncomputable section

open NumberTheory.SharedEEA

/-- Every actual retained-clock inverse rotation precedes the actual parity correction. -/
def finishProgram (modulus : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (SharedEEA.encoding modulus.size).width).toQuantum :=
  (ClockDecode.program modulus.size).seq (OutputCorrection.nativeProgram modulus)

/-- The unchanged native suffix has the complete original corrected source frame. -/
lemma finishProgram_terminal (modulus input : Nat)
    (environment : OracleModel.empty.Interpretation)
    (coprime : Nat.Coprime input modulus) (positive : 0 < input) (bounded : input < modulus) :
    (finishProgram modulus).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((SharedEEA.encoding modulus.size).encode
            (TerminalPosition.frame
              (SharedEEA.NativeSchedule.terminalFrame modulus input positive bounded)
              (QuotientSchedule.padding modulus input))))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((SharedEEA.encoding modulus.size).encode
          (SharedEEA.CorrectedSchedule.result modulus input positive bounded))) := by
  have within := SharedEEA.NativeSchedule.padding_fits modulus input coprime positive bounded
  rw [finishProgram, UnitaryCircuit.applyNormalized_seq,
    (ClockDecode.program_realizes modulus.size).apply_encoded_ket,
    TerminalPosition.decode_word
      (SharedEEA.NativeSchedule.terminalFrame modulus input positive bounded)
      (QuotientSchedule.padding modulus input) within,
    (OutputCorrection.outputCorrection_nativeProgram_realizes modulus).apply_encoded_ket]
  rfl

/-- Actual public pruned loop, full decoder and actual output correction on the same frame. -/
def program (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding modulus.size).width).toQuantum :=
  (PrunedSchedule.program modulus nontrivial).seq
    (UnitaryCircuit.onBinaryPrefix (poolEncoding modulus.size).width (finishProgram modulus))

/-- The actual corrected original word and unchanged entire pool are retained for the adjoint. -/
lemma program_initial (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false) :
    (program modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding modulus.size).encode (InitialFrame.initial modulus input, pool)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding modulus.size).encode
          (SharedEEA.CorrectedSchedule.result modulus input.val positive bounded, pool))) := by
  have firstActual := PrunedSchedule.program_initial modulus nontrivial environment input
    coprime positive bounded pool addressZero prefixZero borrowZero
  have secondActual :=
    UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
      (SharedEEA.encoding modulus.size) (poolEncoding modulus.size) (finishProgram modulus)
      (TerminalPosition.frame
        (SharedEEA.NativeSchedule.terminalFrame modulus input.val positive bounded)
        (QuotientSchedule.padding modulus input.val))
      (SharedEEA.CorrectedSchedule.result modulus input.val positive bounded) pool
      (finishProgram_terminal modulus input.val environment coprime positive bounded)
  exact UnitaryCircuit.applyNormalized_seq_of_eq firstActual secondActual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CorrectedSchedule
