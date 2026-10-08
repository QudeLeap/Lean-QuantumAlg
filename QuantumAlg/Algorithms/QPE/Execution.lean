/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.QPE.Basic
import all QuantumAlg.Algorithms.QPE.Context
import all QuantumAlg.Algorithms.QPE.Storage
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Components.Classical.Model.BitWord.Placement
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# The single complete phase-estimation execution

Actual phase-prefix zero preparation, the source-query unitary, retained phase-result
cells, individual Z writes, and one closed bit-packing instruction execute
in sequence. Complete Output retains the source and phase registers together
with every classical cell; the result is an actual final-store read.
-/

namespace QuantumAlg.QuantumPhaseEstimation

noncomputable section

open QuantumAlg.Execution

def preparationCode {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    Circuit (model P) (pre t n) (preparedContext t n) :=
  .prepareZero (pre t n) ⟨0⟩ (phaseRuntimeLayout t) (preparationFresh t n)
    (preparationDisjoint t n)

def allocationCode {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    Circuit (model P) (preparedContext t n) (post t n) :=
  .seq (.retain (model := model P) (preparedContext t n) ⟨2⟩ (.bits t) (resultFresh t n))
    (MeasurementCells.allocate (model := model P) (resultContext t n) 2 t)

def beforeMeasurement {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    Circuit (model P) (pre t n) (post t n) :=
  .seq (preparationCode P t)
    (.seq (.unitary (nativeProgram P t)) (allocationCode P t))

def readoutCode {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    Circuit (model P) (post t n) (post t n) :=
  .seq (Circuit.measurementSequence (readouts t n)) (.classical (BitWord.application (packing t n)))

/-- One native code value at every width. Width zero still executes the classical packing. -/
def code {n : Nat} (P : QPEEigenstateInput n) (t : Nat) : Circuit (model P) (pre t n) (post t n) :=
  .seq (beforeMeasurement P t) (readoutCode P t)

/-- The explicit complete manifest reads the actual packed phase bits. -/
def run {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    AlgorithmRun (model P) (pre t n) (post t n) (.bits t) where
  code := code P t
  output := Output.all (post t n) (.read (.storage (resultRef t n).toCStorageRef))

theorem run_result {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (record : (run P t).Record) :
    (run P t).result record = record.1.read (.storage (resultRef t n).toCStorageRef) := rfl

theorem run_output_listing {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    (run P t).output.listing = (post t n).keys := rfl

end

end QuantumAlg.QuantumPhaseEstimation
