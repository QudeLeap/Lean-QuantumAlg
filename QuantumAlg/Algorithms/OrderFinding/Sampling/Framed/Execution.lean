/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Storage
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# Actual order sampling around a classical input frame

Fresh preparation and the original source unitary precede actual retained Z
results and a closed packing instruction. Existing classical cells remain in
every intermediate context. The output lists all surviving resources and reads
the actual packed result of this execution.
-/

namespace QuantumAlg.OrderFinding.Sampling.Framed

noncomputable section

open QuantumAlg.Execution

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

def allocationCode (t n : Nat) :
    Circuit (preparedContext ctx noQuantum t n) (post ctx noQuantum t n) :=
  .seq (.retain (preparedContext ctx noQuantum t n)
    (preparedContext ctx noQuantum t n).canonicalFreshKey (.bits t)
    (preparedContext ctx noQuantum t n).canonicalFreshKey_fresh)
    (MeasurementCells.allocate (resultContext ctx noQuantum t n) 2 t)

def beforeMeasurement {N x t n : Nat} (A : ModExpOracleAccess N x t n) :
    Circuit ctx (post ctx noQuantum t n) :=
  .seq (preparationCode ctx noQuantum t n)
    (.seq (.unitary (nativeProgram ctx noQuantum A) (nativeProgram_placement ctx noQuantum A))
      (allocationCode ctx noQuantum t n))

def readoutCode (t n : Nat) :
    Circuit (post ctx noQuantum t n) (post ctx noQuantum t n) :=
  .seq (Circuit.measurementSequence (readouts ctx noQuantum t n))
    (.classical (packing ctx noQuantum t n))

/-- The one actual source sample preserves its caller's existing classical storage. -/
def code {N x t n : Nat} (A : ModExpOracleAccess N x t n) :
    Circuit ctx (post ctx noQuantum t n) :=
  .seq (beforeMeasurement ctx noQuantum A) (readoutCode ctx noQuantum t n)

/-- Complete output retains the caller frame, quantum wires and each classical measurement cell. -/
def run {N x t n : Nat} (A : ModExpOracleAccess N x t n) :
    AlgorithmRun ctx (post ctx noQuantum t n) (.bits t) where
  code := code ctx noQuantum A
  output := Output.all (post ctx noQuantum t n)
    (.read (.storage (resultRef ctx noQuantum t n).toCStorageRef))

theorem run_result {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (record : (run ctx noQuantum A).Record) :
    (run ctx noQuantum A).result record =
      record.1.read (.storage (resultRef ctx noQuantum t n).toCStorageRef) := rfl

theorem run_output_listing {N x t n : Nat} (A : ModExpOracleAccess N x t n) :
    (run ctx noQuantum A).output.listing = (post ctx noQuantum t n).keys := rfl

end

end QuantumAlg.OrderFinding.Sampling.Framed
