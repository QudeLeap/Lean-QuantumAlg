/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native
import all QuantumAlg.Core.Execution.FiniteReadout
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Measurement.Cells.Frame
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# Actual finite-cyclic readouts agree with the original terminal measurement

Distinct exponent positions write distinct retained two-valued cells. Their
original order reads exactly the original terminal bit string. The comparison
uses each physical wire value, including the original bit significance, and
introduces no packing instruction or additional storage. Incoming structural
operands keep their values through every actual measurement write.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical
namespace GateLevelAttempt.Native

open Execution

noncomputable section

universe u

variable {G : Type u} [Group G]
  (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (P : KnownOrderProblem G)

private theorem readout_key (index : Fin (sampleWidth P)) :
    (readout base noQuantum P index).output.key = (cells base noQuantum P index).key :=
  FiniteReadout.transported_key
    (nativeFiniteCyclic_context_qubits P (nativeFiniteCyclic_context_wires base noQuantum P) _)
    (cells base noQuantum P index)

private theorem readout_value (index : Fin (sampleWidth P))
    (store : Store (context base noQuantum P)) :
    (store.read (.storage (readout base noQuantum P index).output.toCStorageRef)).toFin.val =
      (store.read (.storage (cells base noQuantum P index).toCStorageRef)).toFin.val :=
  FiniteReadout.transported_read_value
    (nativeFiniteCyclic_context_qubits P (nativeFiniteCyclic_context_wires base noQuantum P) _)
    (cells base noQuantum P index) store

/-- The actual readout sequence has one distinct retained destination per exponent position. -/
theorem nativeFiniteCyclic_readouts_nodup :
    ((readouts base noQuantum P).map fun item => item.output.key).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right same
  have keys := (readout_key base noQuantum P left).symm.trans
    (same.trans (readout_key base noQuantum P right))
  exact MeasurementCells.reference_key_injective _ _ _ keys

/-- The actual terminal cell stores the finite value of its corresponding measured wire. -/
theorem nativeFiniteCyclic_measured_cell (store : Store (context base noQuantum P))
    (basis : (context base noQuantum P).register.Index) (index : Fin (sampleWidth P)) :
    ((Circuit.writeMeasurementPath (readouts base noQuantum P) store
      (Circuit.measurementBasisPath (readouts base noQuantum P) basis)).read
        (.storage (cells base noQuantum P index).toCStorageRef)).toFin.val =
      (basis (readout base noQuantum P index).wire).val := by
  have actual := Circuit.writeMeasurementBasis_read (readouts base noQuantum P)
    (nativeFiniteCyclic_readouts_nodup base noQuantum P) (readout base noQuantum P index)
    (List.mem_ofFn.mpr ⟨index, rfl⟩) store basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  rw [readout_value] at numeric
  exact numeric

private theorem wire_value (basis : (context base noQuantum P).register.Index)
    (index : Fin (totalQubits P)) :
    (basis (wireEquiv P (nativeFiniteCyclic_context_wires base noQuantum P) index)).val =
      ((layout P).binaryIndexEquiv.symm
        (basisEquiv P (nativeFiniteCyclic_context_wires base noQuantum P) basis) index).val := by
  let correspondence := Execution.basisOfEqualWires (bankLayout P)
    (context base noQuantum P).quantumLayout
    (layoutWires P (nativeFiniteCyclic_context_wires base noQuantum P))
  have value := Execution.basisOfEqualWires_value (bankLayout P)
    (context base noQuantum P).quantumLayout
    (layoutWires P (nativeFiniteCyclic_context_wires base noQuantum P))
    (correspondence.symm basis) index
  change (correspondence (correspondence.symm basis)
    (wireEquiv P (nativeFiniteCyclic_context_wires base noQuantum P) index)).val = _ at value
  rw [Equiv.apply_symm_apply] at value
  have inverse := Equiv.symm_apply_apply (layout P).binaryIndexEquiv
    (correspondence.symm basis)
  exact value.trans (congrArg
    (fun source : (layout P).toQuantumLayout.Basis => (source index).val) inverse).symm

/-- The stored exponent bits have exactly the original terminal measurement's significance. -/
theorem nativeFiniteCyclic_measured_bit (store : Store (context base noQuantum P))
    (basis : (context base noQuantum P).register.Index) (index : Fin (sampleWidth P)) :
    decide ((((Circuit.writeMeasurementPath (readouts base noQuantum P) store
      (Circuit.measurementBasisPath (readouts base noQuantum P) basis)).read
        (.storage (cells base noQuantum P index).toCStorageRef)).toFin.val) = 1) =
      (terminalMeasurement P).readout
        (basisEquiv P (nativeFiniteCyclic_context_wires base noQuantum P) basis) index := by
  rw [nativeFiniteCyclic_measured_cell]
  let source := (terminalMeasurement P).logical_idx index
  let binary := basisEquiv P (nativeFiniteCyclic_context_wires base noQuantum P) basis
  have finiteValue := wire_value base noQuantum P basis source
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

/-- The actual measurement writes preserve every structural operand from before allocation. -/
theorem nativeFiniteCyclic_measured_input {shape : CShape} (input : CInputRef base shape)
    (store : Store (context base noQuantum P)) (basis : (context base noQuantum P).register.Index) :
    (Circuit.writeMeasurementPath (readouts base noQuantum P) store
      (Circuit.measurementBasisPath (readouts base noQuantum P) basis)).read
        (liftInput base noQuantum P input) = store.read (liftInput base noQuantum P input) := by
  apply Circuit.writeMeasurementPath_read_input
  intro item present
  obtain ⟨position, rfl⟩ := List.mem_ofFn.mp present
  rw [readout_key]
  exact MeasurementCells.reference_not_mem_liftInput 2 _ (sampleWidth P) position

end

end GateLevelAttempt.Native
end QuantumAlg.FiniteCyclicDLP.Canonical
