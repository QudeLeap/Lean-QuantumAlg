/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Basic
import all QuantumAlg.Algorithms.AmplitudeEstimation.Context
import all QuantumAlg.Algorithms.AmplitudeEstimation.Storage
import all QuantumAlg.Components.Classical.Model.BitWord.Placement
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# The single complete amplitude-estimation execution

Actual all-zero preparation, the source-query unitary, retained phase-result
cells, individual Z writes, and one closed bit-packing instruction execute
in sequence. Complete Output retains the source and phase registers together
with every classical cell; the result is an actual final-store read.
-/

namespace QuantumAlg.AmplitudeEstimation

noncomputable section

open QuantumAlg.Execution

def preparationCode (n : Nat) (t : Nat) :
    Circuit (model n) pre (preparedContext t n) :=
  .prepareZero pre ⟨0⟩ (runtimeLayout t n) preparationFresh (preparationDisjoint t n)

def allocationCode (n : Nat) (t : Nat) :
    Circuit (model n) (preparedContext t n) (post t n) :=
  .seq (.retain (model := model n) (preparedContext t n) ⟨1⟩ (.bits t) (resultFresh t n))
    (MeasurementCells.allocate (model := model n) (resultContext t n) 2 t)

def beforeMeasurement (n : Nat) (t : Nat) :
    Circuit (model n) pre (post t n) :=
  .seq (preparationCode n t)
    (.seq (.unitary (nativeProgram n t)) (allocationCode n t))

def readoutCode (n : Nat) (t : Nat) :
    Circuit (model n) (post t n) (post t n) :=
  .seq (Circuit.measurementSequence (readouts t n)) (.classical (BitWord.application (packing t n)))

/-- The full actual word prepares existing qubits and performs explicit classical packing. -/
def code (n : Nat) (t : Nat) :
    Circuit (model n) pre (post t n) :=
  .seq (beforeMeasurement n t) (readoutCode n t)

/-- The explicit complete manifest reads the actual packed phase bits. -/
def run (n : Nat) (t : Nat) :
    AlgorithmRun (model n) pre (post t n) (.bits t) where
  code := code n t
  output := Output.all (post t n) (.read (.storage (resultRef t n).toCStorageRef))

lemma run_result (n : Nat) (t : Nat)
    (record : (run n t).Record) :
    (run n t).result record = record.1.read (.storage (resultRef t n).toCStorageRef) := rfl

lemma run_output_listing (n : Nat) (t : Nat) :
    (run n t).output.listing = (post t n).keys := rfl

end

end QuantumAlg.AmplitudeEstimation
