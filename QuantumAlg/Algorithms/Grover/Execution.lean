/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace

import all QuantumAlg.Algorithms.Grover.Context
import all QuantumAlg.Algorithms.Grover.Storage
import all QuantumAlg.Components.Classical.Model.BitWord.Placement
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

/-- Zero preparation charges every actually allocated source and helper system. -/
def preparationCode (n : Nat) (k : Nat) :
    Circuit (model n) pre (preparedContext (totalQubits n k)) :=
  .prepareZero pre ⟨1⟩ (runtimeLayout (totalQubits n k)) preparationFresh
    (preparationDisjoint (totalQubits n k))

/-- Retain the packed result and all independently written binary measurement cells. -/
def allocationCode (n : Nat) (k : Nat) :
    Circuit (model n) (preparedContext (totalQubits n k)) (post n k) :=
  .seq (.retain (model := model n) (preparedContext (totalQubits n k))
    ⟨2⟩ (.bits n) (resultFresh n k))
    (MeasurementCells.allocate (model := model n) (resultContext n k) 2 n)

/-- Execute the actual native search word before any result measurement. -/
def beforeMeasurement (n : Nat) (k : Nat) :
    Circuit (model n) pre (post n k) :=
  .seq (preparationCode n k)
    (.seq (.unitary (program n k)) (allocationCode n k))

/-- Record all source Z outcomes, then pack those actual values with a declared native operation. -/
def readoutCode (n : Nat) (k : Nat) :
    Circuit (model n) (post n k) (post n k) :=
  .seq (Circuit.measurementSequence (readouts n k))
    (.classical (BitWord.application (packing n k)))

/-- One native complete program at every width and iteration count. -/
def code (n : Nat) (k : Nat) :
    Circuit (model n) pre (post n k) :=
  .seq (beforeMeasurement n k) (readoutCode n k)

/-- Output retains every live cell and wire and observes the actual packed result. -/
def run (n : Nat) (k : Nat) :
    AlgorithmRun (model n) pre (post n k) (.bits n) where
  code := code n k
  output := Output.all (post n k) (.read (.storage (resultRef n k).toCStorageRef))

/-- The result is the value in the actual retained bit-string cell. -/
lemma run_result (n : Nat) (k : Nat)
    (record : (run n k).Record) :
    (run n k).result record = record.1.read (.storage (resultRef n k).toCStorageRef) := rfl

/-- Every live storage key is retained in the explicit complete output. -/
lemma run_output_listing (n : Nat) (k : Nat) :
    (run n k).output.listing = (post n k).keys := rfl

end

end QuantumAlg.GroverSearch
