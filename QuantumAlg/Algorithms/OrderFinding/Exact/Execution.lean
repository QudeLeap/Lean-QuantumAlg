/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Oracle
import all QuantumAlg.Algorithms.OrderFinding.Exact.Context
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Execution
import all QuantumAlg.Components.Classical.TerminalDecode.Circuit
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# Actual order sampling followed by stored-bit terminal decoding

One original sampling circuit prepares, applies its source-query unitary,
measures the phase wires and packs their real stored values. The existing
fixed-width decoder then reads those bits, executes its shift and conditional
increment instructions, and materializes the returned unsigned word. All live
quantum and classical resources appear in the complete Output.
-/

namespace QuantumAlg.OrderFinding.Exact

noncomputable section

/-- Allocate the unsigned result, then decode the actual packed measurement bits. -/
def decoderCode (t n : Nat) : Circuit (Sampling.post t n) (post t n) :=
  ClassicalRoutines.TerminalDecode.routine
    (Sampling.post t n) t .bigEndian (packedInput t n) (resultKey t n) (resultFresh t n)

/-- One uniform complete execution at every phase and target width. -/
def code {N x t n : Nat} (A : ModExpOracleAccess N x t n) :
    Circuit Sampling.pre (post t n) :=
  .seq (Sampling.code A) (decoderCode t n)

/-- The result is a stored unsigned word; every source resource is retained. -/
def run {N x t n : Nat} (A : ModExpOracleAccess N x t n) :
    AlgorithmRun Sampling.pre (post t n) (.unsignedWord t) where
  code := code A
  output := QuantumAlg.Output.all (post t n) (.read (resultRef t n))

theorem run_result {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (record : (run A).Record) :
    (run A).result record = record.1.read (resultRef t n) := rfl

theorem run_output_listing {N x t n : Nat} (A : ModExpOracleAccess N x t n) :
    (run A).output.listing = (post t n).keys := rfl

end

end QuantumAlg.OrderFinding.Exact
