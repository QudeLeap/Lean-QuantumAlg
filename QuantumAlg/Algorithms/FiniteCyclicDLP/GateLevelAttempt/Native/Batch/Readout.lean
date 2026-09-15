/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Batch
import all QuantumAlg.Core.Execution.FiniteReadout
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Measurement.Cells.Frame
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# Each retained finite-cyclic sample is the original terminal readout

Distinct exponent positions write distinct retained two-valued cells. Their
original order reads exactly the original terminal bit string. The comparison
uses each physical wire value, including the original bit significance, and
introduces no packing instruction or additional storage. Incoming structural
operands keep their values through every actual measurement write.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical
namespace GateLevelAttempt.Native.Batch

open Execution

noncomputable section

universe u

variable {G : Type u} [Group G]
  (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (P : KnownOrderProblem G) (count : Nat) (slot : Fin count)

private theorem readout_value (index : Fin (sampleWidth P))
    (store : Store (context base noQuantum P count)) :
    (store.read (.storage (readout base noQuantum P count slot
      index).output.toCStorageRef)).toFin.val =
      (store.read (.storage (cells base noQuantum P count slot index).toCStorageRef)).toFin.val :=
  FiniteReadout.transported_read_value
    (nativeFiniteCyclic_context_qubits P (nativeFiniteCyclicBatch_context_wires base noQuantum P
      count) _)
    (cells base noQuantum P count slot index) store

/-- The actual terminal cell stores the finite value of its corresponding measured wire. -/
theorem nativeFiniteCyclicBatch_measured_cell (store : Store (context base noQuantum P count))
    (basis : (context base noQuantum P count).register.Index) (index : Fin (sampleWidth P)) :
    ((Circuit.writeMeasurementPath (readouts base noQuantum P count slot) store
      (Circuit.measurementBasisPath (readouts base noQuantum P count slot) basis)).read
        (.storage (cells base noQuantum P count slot index).toCStorageRef)).toFin.val =
      (basis (readout base noQuantum P count slot index).wire).val := by
  have actual := Circuit.writeMeasurementBasis_read (readouts base noQuantum P count slot)
    (nativeFiniteCyclicBatch_readouts_nodup base noQuantum P count slot) (readout base noQuantum P
      count slot index)
    (List.mem_ofFn.mpr ⟨index, rfl⟩) store basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  rw [readout_value] at numeric
  exact numeric

private theorem wire_value (basis : (context base noQuantum P count).register.Index)
    (index : Fin (totalQubits P)) :
    (basis (wireEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count) index)).val =
      ((layout P).binaryIndexEquiv.symm
        (basisEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count) basis)
          index).val := by
  let correspondence := Execution.basisOfEqualWires (bankLayout P)
    (context base noQuantum P count).quantumLayout
    (layoutWires P (nativeFiniteCyclicBatch_context_wires base noQuantum P count))
  have value := Execution.basisOfEqualWires_value (bankLayout P)
    (context base noQuantum P count).quantumLayout
    (layoutWires P (nativeFiniteCyclicBatch_context_wires base noQuantum P count))
    (correspondence.symm basis) index
  change (correspondence (correspondence.symm basis)
    (wireEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count) index)).val = _
    at value
  rw [Equiv.apply_symm_apply] at value
  have inverse := Equiv.symm_apply_apply (layout P).binaryIndexEquiv
    (correspondence.symm basis)
  exact value.trans (congrArg
    (fun source : (layout P).toQuantumLayout.Basis => (source index).val) inverse).symm

/-- The stored exponent bits have exactly the original terminal measurement's significance. -/
theorem nativeFiniteCyclicBatch_measured_bit (store : Store (context base noQuantum P count))
    (basis : (context base noQuantum P count).register.Index) (index : Fin (sampleWidth P)) :
    decide ((((Circuit.writeMeasurementPath (readouts base noQuantum P count slot) store
      (Circuit.measurementBasisPath (readouts base noQuantum P count slot) basis)).read
        (.storage (cells base noQuantum P count slot index).toCStorageRef)).toFin.val) = 1) =
      (terminalMeasurement P).readout
        (basisEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count) basis)
          index := by
  rw [nativeFiniteCyclicBatch_measured_cell]
  let source := (terminalMeasurement P).logical_idx index
  let binary := basisEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count) basis
  have finiteValue := wire_value base noQuantum P count basis source
  have bit := (layout P).binaryIndexEquiv_bit
    ((layout P).binaryIndexEquiv.symm binary) source
  rw [Equiv.apply_symm_apply] at bit
  have converted (value : Fin 2) : decide (value.val = 1) = finTwoEquiv value := by
    fin_cases value <;> rfl
  calc
    _ = finTwoEquiv ((layout P).binaryIndexEquiv.symm binary source) :=
      (congrArg (fun value => decide (value = 1)) finiteValue).trans (converted _)
    _ = binary.val.testBit source.rev.val := bit.symm
    _ = _ := by
      change binary.val.testBit source.rev.val =
        binary.val.testBit (totalQubits P - 1 - source.val)
      congr 1
      simp only [Fin.rev]
      omega

/-- Only actual measurement destinations constrain a preserved structural read. -/
theorem nativeFiniteCyclicBatch_measured_input {shape : CShape}
    (input : CInputRef (context base noQuantum P count) shape)
    (separate : ∀ index : Fin (sampleWidth P),
      (cells base noQuantum P count slot index).key ∉ input.storageKeys)
    (store : Store (context base noQuantum P count))
    (basis : (context base noQuantum P count).register.Index) :
    (Circuit.writeMeasurementPath (readouts base noQuantum P count slot) store
      (Circuit.measurementBasisPath (readouts base noQuantum P count slot) basis)).read input =
      store.read input := by
  apply Circuit.writeMeasurementPath_read_input
  intro item present
  obtain ⟨position, rfl⟩ := List.mem_ofFn.mp present
  rw [nativeFiniteCyclicBatch_readout_key]
  exact separate position

end

end GateLevelAttempt.Native.Batch
end QuantumAlg.FiniteCyclicDLP.Canonical
