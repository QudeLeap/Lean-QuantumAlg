/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace

import all QuantumAlg.Algorithms.Grover.Context
import all QuantumAlg.Algorithms.Grover.Storage
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# The single complete Grover execution

One actual basis preparation, the exact phase-oracle/diffusion circuit,
retained result cells, n individual Z writes, and one closed packing opcode
form the sole executable program. Its explicit Output retains every live
entry and reads the actual packed index. No outcome PMF or resource witness
is stored with the program.

-/

namespace QuantumAlg.GroverSearch

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

open QuantumAlg.Execution

/-- Prepare the owned search register through the real preparation instruction. -/
def preparationCode (n : Nat) : Circuit pre (preparedContext n) :=
  .prepare pre ⟨1⟩ (runtimeLayout n) preparationFresh
    (preparationDisjoint n) (inputPreparation n)

/-- Retain the final bit string and every independently writable measured-result cell. -/
def allocationCode (n k : Nat) :
    Circuit (preparedContext (totalQubits n k)) (post n k) :=
  .seq (.retain (preparedContext (totalQubits n k)) ⟨2⟩ (.bits n) (resultFresh n k))
    (MeasurementCells.allocate (resultContext n k) 2 n)

/-- The actual state immediately before the first search-wire measurement. -/
def beforeMeasurement {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) : Circuit pre (post n k) :=
  .seq (preparationCode (totalQubits n k))
    (.seq (.unitary (program marked k) (program_placement marked k)) (allocationCode n k))

/-- Record every measured search bit, then pack those actual finite values into the final result. -/
def readoutCode (n k : Nat) : Circuit (post n k) (post n k) :=
  .seq (Circuit.measurementSequence (readouts n k)) (.classical (packing n k))

/-- One native program for every width, including the empty query register. -/
def code {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) : Circuit pre (post n k) :=
  .seq (beforeMeasurement marked k) (readoutCode n k)

/-- The explicit complete manifest observes the actual packed result cell. -/
def run {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    AlgorithmRun pre (post n k) (.bits n) where
  code := code marked k
  output := Output.all (post n k) (.read (.storage (resultRef n k).toCStorageRef))

/-- The result is the value in the actual retained bit-string cell. -/
theorem run_result {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (record : (run marked k).Record) :
    (run marked k).result record = record.1.read (.storage (resultRef n k).toCStorageRef) := rfl

/-- Every live storage key is retained in the explicit complete output. -/
theorem run_output_listing {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    (run marked k).output.listing = (post n k).keys := rfl

end

end QuantumAlg.GroverSearch
