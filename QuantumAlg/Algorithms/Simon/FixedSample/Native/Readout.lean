/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Native
import all QuantumAlg.Core.Execution.FiniteReadout
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Readout

/-!
# Actual complete first-register writes of the fixed Simon sampler

The n original distinct finite cells receive exactly the corresponding
physical first-register values. These storage facts precede both the Born
law and the complete-state comparison of reusable reset protocols.
-/

namespace QuantumAlg.SimonsProblem.FixedSample.Native

open Execution

noncomputable section

variable {oracles : OracleModel}
variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (n count : Nat)

private lemma readout_key (index : Fin n) :
    (readout base noQuantum n count index).output.key = (cells base noQuantum n count index).key :=
  FiniteReadout.transported_key
    (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count) _)
    (cells base noQuantum n count index)

private lemma readout_value (index : Fin n)
    (store : Store (context base noQuantum n count)) :
    (store.read (.storage (readout base noQuantum n count index).output.toCStorageRef)).toFin.val =
      (store.read (.storage (cells base noQuantum n count index).toCStorageRef)).toFin.val :=
  FiniteReadout.transported_read_value
    (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count) _)
    (cells base noQuantum n count index) store

private lemma readouts_nodup :
    ((readouts base noQuantum n count).map fun item => item.output.key).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right same
  have keys := (readout_key base noQuantum n count left).symm.trans
    (same.trans (readout_key base noQuantum n count right))
  exact MeasurementCells.reference_key_injective _ _ _ keys

private lemma measured_cell (store : Store (context base noQuantum n count))
    (basis : (context base noQuantum n count).register.Index) (index : Fin n) :
    ((Circuit.writeMeasurementPath (allowAllocation := true)
      (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := .empty)
        (readouts base noQuantum n count) store
      (Circuit.measurementBasisPath (allowAllocation := true)
      (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := .empty)
        (readouts base noQuantum n count) basis)).read
        (.storage (cells base noQuantum n count index).toCStorageRef)).toFin.val =
      (basis (readout base noQuantum n count index).wire).val := by
  have actual := Circuit.writeMeasurementBasis_read (allowAllocation := true)
      (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (services := .empty)
        (readouts base noQuantum n count)
    (readouts_nodup base noQuantum n count) (readout base noQuantum n count index)
    (List.mem_ofFn.mpr ⟨index, rfl⟩) store basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  rw [readout_value] at numeric
  exact numeric

end

end QuantumAlg.SimonsProblem.FixedSample.Native
