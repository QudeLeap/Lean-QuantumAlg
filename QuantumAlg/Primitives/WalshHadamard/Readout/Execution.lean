/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.WalshHadamard.Readout.Context
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# The single complete Walsh-Hadamard query readout execution

The executable preparation, original XOR-query circuit, actual storage
allocations, individual Z measurements, and charged packing instruction are
sequentially composed below. The complete output retains the prepared query
and target systems, measured finite cells, final bit string, and borrowed
unit input. No independently prescribed outcome distribution is stored here.
-/

namespace QuantumAlg.WalshHadamard.Readout

noncomputable section

open QuantumAlg.Execution

/-- Prepare the owned query-target register through the real preparation instruction. -/
def preparationCode (n : Nat) : Circuit pre (preparedContext n) :=
  .prepare pre ⟨1⟩ (runtimeLayout n) preparationFresh
    (preparationDisjoint n) (inputPreparation n)

/-- Retain the final bit string and every independently writable measured-result cell. -/
def allocationCode (n : Nat) : Circuit (preparedContext n) (post n) :=
  .seq (.retain (preparedContext n) ⟨2⟩ (.bits n) (resultFresh n))
    (MeasurementCells.allocate (resultContext n) 2 n)

/-- The actual state immediately before the first query-wire measurement. -/
def beforeMeasurement {n : Nat} (f : WalshHadamard.Oracle n) : Circuit pre (post n) :=
  .seq (preparationCode n)
    (.seq (.unitary (program f) (program_placement f)) (allocationCode n))

/-- Record every measured query bit, then pack those actual finite values into the final result. -/
def readoutCode (n : Nat) : Circuit (post n) (post n) :=
  .seq (Circuit.measurementSequence (readouts n)) (.classical (packing n))

/-- One native program for every width, including the empty query register. -/
def code {n : Nat} (f : WalshHadamard.Oracle n) : Circuit pre (post n) :=
  .seq (beforeMeasurement f) (readoutCode n)

/-- The explicit complete manifest observes the actual packed result cell. -/
def run {n : Nat} (f : WalshHadamard.Oracle n) : AlgorithmRun pre (post n) (.bits n) where
  code := code f
  output := Output.all (post n) (.read (.storage (resultRef n).toCStorageRef))

/-- The result is the value in the actual retained bit-string cell. -/
theorem run_result {n : Nat} (f : WalshHadamard.Oracle n) (record : (run f).Record) :
    (run f).result record = record.1.read (.storage (resultRef n).toCStorageRef) := rfl

/-- Every live storage key is retained in the explicit complete output. -/
theorem run_output_listing {n : Nat} (f : WalshHadamard.Oracle n) :
    (run f).output.listing = (post n).keys := rfl

end

end QuantumAlg.WalshHadamard.Readout
