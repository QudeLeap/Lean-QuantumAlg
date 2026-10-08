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

def preparationCode {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    Circuit (model E) pre (preparedContext t n) :=
  .prepareZero pre ⟨0⟩ (runtimeLayout t n) preparationFresh (preparationDisjoint t n)

def allocationCode {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    Circuit (model E) (preparedContext t n) (post t n) :=
  .seq (.retain (model := model E) (preparedContext t n) ⟨1⟩ (.bits t) (resultFresh t n))
    (MeasurementCells.allocate (model := model E) (resultContext t n) 2 t)

def beforeMeasurement {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    Circuit (model E) pre (post t n) :=
  .seq (preparationCode E t)
    (.seq (.unitary (nativeProgram E t)) (allocationCode E t))

def readoutCode {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    Circuit (model E) (post t n) (post t n) :=
  .seq (Circuit.measurementSequence (readouts t n)) (.classical (BitWord.application (packing t n)))

/-- The full actual word prepares existing qubits and performs explicit classical packing. -/
def code {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    Circuit (model E) pre (post t n) :=
  .seq (beforeMeasurement E t) (readoutCode E t)

/-- The explicit complete manifest reads the actual packed phase bits. -/
def run {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    AlgorithmRun (model E) pre (post t n) (.bits t) where
  code := code E t
  output := Output.all (post t n) (.read (.storage (resultRef t n).toCStorageRef))

theorem run_result {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    (record : (run E t).Record) :
    (run E t).result record = record.1.read (.storage (resultRef t n).toCStorageRef) := rfl

theorem run_output_listing {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    (run E t).output.listing = (post t n).keys := rfl

end

end QuantumAlg.AmplitudeEstimation
