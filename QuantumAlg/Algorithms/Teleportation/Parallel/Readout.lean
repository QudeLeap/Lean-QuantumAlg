/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Teleportation.Parallel.Construction
import all QuantumAlg.Algorithms.Teleportation.Parallel.Construction
import all QuantumAlg.Algorithms.Teleportation.Parallel.Geometry
import all QuantumAlg.Core.Execution.QubitReadouts
import all QuantumAlg.Core.Execution.Measurement.Readout

/-!
# Feedback selectors are exactly the actual measured bits

Both correction selectors are read from the real result cells written by
the measurement interpreter. Distinct destination keys ensure that later
readouts do not overwrite an earlier block's bit [dW19, qcnotes.tex:802,804].
The original store and quantum basis are arbitrary; no initial classical
result or independent outcome parameter is assumed.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel

noncomputable section

open Execution

/-- The actual sequence of writes for the measurement path determined by a physical basis. -/
def writtenStore (count : Nat) (store : Store (context count))
    (basis : (context count).register.Index) : Store (context count) :=
  Circuit.writeMeasurementPath (allowAllocation := false) (gates := AlgorithmGate.model)
    (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
    (readouts count) store
    (Circuit.measurementBasisPath (allowAllocation := false) (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
      (readouts count) basis)

/-- Every destination contains the computational label of its own original Alice system. -/
lemma writtenStore_value (count : Nat) (store : Store (context count))
    (basis : (context count).register.Index) (index : Fin (count * 2)) :
    ((writtenStore count store basis).read
      (.storage (resultCell count index).toCStorageRef)).toFin.val =
        (basis (measuredPosition count index)).val :=
  QubitReadouts.written_value (allowAllocation := false) (gates := AlgorithmGate.model)
    (oracles := .empty) (operations := .empty) (services := .empty)
    (measuredPosition count) (measuredPosition_dimension count)
    (resultCell count) (resultCell_key_injective count) store basis index

/-- The complete selector table is obtained from the actual writes in the same execution. -/
lemma storedBits_writtenStore (count : Nat) (store : Store (context count))
    (basis : (context count).register.Index) (block : Fin count) :
    storedBits ((writtenStore count store basis).read (resultInput count)) block =
      (decide ((basis (measuredPosition count (finProdFinEquiv (block, 0)))).val = 1),
        decide ((basis (measuredPosition count (finProdFinEquiv (block, 1)))).val = 1)) := by
  apply Prod.ext
  · exact congrArg (fun value : Nat => decide (value = 1))
      (writtenStore_value count store basis (finProdFinEquiv (block, 0)))
  · exact congrArg (fun value : Nat => decide (value = 1))
      (writtenStore_value count store basis (finProdFinEquiv (block, 1)))

/-- The selected native correction reads precisely the measured basis labels of Alice's wires. -/
lemma selectedCorrection_writtenStore (count : Nat) (store : Store (context count))
    (basis : (context count).register.Index) :
    selectedCorrection count ((writtenStore count store basis).read (resultInput count)) =
      onContext count (correctionWord count (fun block =>
        (decide ((basis (measuredPosition count (finProdFinEquiv (block, 0)))).val = 1),
          decide ((basis (measuredPosition count (finProdFinEquiv (block, 1)))).val = 1)))) := by
  unfold selectedCorrection
  apply congrArg (fun bits => onContext count (correctionWord count bits))
  funext block
  exact storedBits_writtenStore count store basis block

end

end QuantumAlg.QuantumTeleportation.Parallel
