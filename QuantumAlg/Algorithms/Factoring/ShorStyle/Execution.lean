/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Context
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch.Prepared
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Layout
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Output

/-!
# One actual complete Shor circuit through recovery and final output

The single preparation precedes the same-bank sampling rounds, then the real
result allocation and native first-success recovery scan. Every surviving
quantum and classical entry occurs in the complete output listing. The source
input supplies only the public modulus proofs; no source distribution or
mathematical recovery result is an executable argument.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint

noncomputable section

/-- Native recovery consumes the same actual retained tuple references beneath four true heads. -/
def recoveryCode {N : Nat} (source : Input N) (count : Nat) :
    Circuit (post N count) (post N count) :=
  NativeFactorScan.Scope.code source (visitInputs N count) (resultRef N count)

/-- Real allocation of the result precedes the full native factor scan. -/
def recoveryStage {N : Nat} (source : Input N) (count : Nat) :
    Circuit (sampledContext N count) (post N count) :=
  .seq (.retain (sampledContext N count) (resultKey N count) (outputShape N) (resultFresh N count))
    (recoveryCode source count)

/-- One interpreter executes the bank, every source round and the full native recovery tail. -/
def code {N : Nat} (source : Input N) (count : Nat) : Circuit pre (post N count) :=
  .seq (NativePreparedBatch.code pre pre_quantumWires N count) (recoveryStage source count)

/-- Complete output reads the final optional factor while retaining all other live entries. -/
def run {N : Nat} (source : Input N) (count : Nat) :
    AlgorithmRun pre (post N count) (outputShape N) where
  code := code source count
  output := Output.all (post N count) (.read (.storage (resultRef N count).toCStorageRef))

theorem run_output_listing {N : Nat} (source : Input N) (count : Nat) :
    (run source count).output.listing = (post N count).keys := rfl

/-- The public result value is exactly the content of the cell written by the real final pack. -/
theorem run_result {N : Nat} (source : Input N) (count : Nat)
    (record : (run source count).Record) :
    (run source count).result record = record.1.read (.storage (resultRef N count).toCStorageRef) :=
  rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint
