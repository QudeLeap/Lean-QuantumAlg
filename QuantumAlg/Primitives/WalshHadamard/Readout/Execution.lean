/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.WalshHadamard.Readout.Context
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Components.Classical.Model.BitWord.Placement
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
def preparationCode (n : Nat) :
    Circuit (model n) pre (preparedContext n) :=
  .prepareZero pre ⟨1⟩ (runtimeLayout n) preparationFresh (preparationDisjoint n)

/-- Retain the final bit string and every independently writable measured-result cell. -/
def allocationCode (n : Nat) :
    Circuit (model n) (preparedContext n) (post n) :=
  .seq (.retain (model := model n) (preparedContext n) ⟨2⟩ (.bits n) (resultFresh n))
    (MeasurementCells.allocate (model := model n) (resultContext n) 2 n)

/-- The actual state immediately before the first query-wire measurement. -/
def beforeMeasurement (n : Nat) : Circuit (model n) pre (post n) :=
  .seq (preparationCode n)
    (.seq (.unitary (program n)) (allocationCode n))

/-- Record every measured query bit, then pack those actual finite values into the final result. -/
def readoutCode (n : Nat) :
    Circuit (model n) (post n) (post n) :=
  .seq (Circuit.measurementSequence (readouts n)) (.classical (BitWord.application (packing n)))

/-- One native program for every width, including the empty query register. -/
def code (n : Nat) : Circuit (model n) pre (post n) :=
  .seq (beforeMeasurement n) (readoutCode n)

/-- The explicit complete manifest observes the actual packed result cell. -/
def run (n : Nat) : AlgorithmRun (model n) pre (post n) (.bits n) where
  code := code n
  output := Output.all (post n) (.read (.storage (resultRef n).toCStorageRef))

/-- The result is the value in the actual retained bit-string cell. -/
lemma run_result (n : Nat) (record : (run n).Record) :
    (run n).result record = record.1.read (.storage (resultRef n).toCStorageRef) := rfl

/-- Every live storage key is retained in the explicit complete output. -/
lemma run_output_listing (n : Nat) :
    (run n).output.listing = (post n).keys := rfl

end

end QuantumAlg.WalshHadamard.Readout
