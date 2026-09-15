/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native
import all QuantumAlg.Core.Execution.FiniteReadout
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Measurement.Cells.Frame
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# Actual finite ECDLP readouts agree with the original terminal measurement

Distinct exponent positions write distinct retained two-valued cells. Their
original order reads exactly the original terminal bit string. The comparison
uses each physical wire value, including the original bit significance, and
introduces no packing instruction or additional storage. Incoming structural
operands keep their values through every actual measurement write.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

open Execution

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}
  (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)

private theorem readout_key (index : Fin (sampleWidth I)) :
    (readout base noQuantum I index).output.key = (cells base noQuantum I index).key :=
  FiniteReadout.transported_key
    (nativeECDLP_context_qubits I (nativeECDLP_context_wires base noQuantum I) _)
    (cells base noQuantum I index)

private theorem readout_value (index : Fin (sampleWidth I))
    (store : Store (context base noQuantum I)) :
    (store.read (.storage (readout base noQuantum I index).output.toCStorageRef)).toFin.val =
      (store.read (.storage (cells base noQuantum I index).toCStorageRef)).toFin.val :=
  FiniteReadout.transported_read_value
    (nativeECDLP_context_qubits I (nativeECDLP_context_wires base noQuantum I) _)
    (cells base noQuantum I index) store

/-- The actual readout sequence has one distinct retained destination per exponent position. -/
theorem nativeECDLP_readouts_nodup :
    ((readouts base noQuantum I).map fun item => item.output.key).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right same
  have keys := (readout_key base noQuantum I left).symm.trans
    (same.trans (readout_key base noQuantum I right))
  exact MeasurementCells.reference_key_injective _ _ _ keys

/-- The actual terminal cell stores the finite value of its corresponding measured wire. -/
theorem nativeECDLP_measured_cell (store : Store (context base noQuantum I))
    (basis : (context base noQuantum I).register.Index) (index : Fin (sampleWidth I)) :
    ((Circuit.writeMeasurementPath (readouts base noQuantum I) store
      (Circuit.measurementBasisPath (readouts base noQuantum I) basis)).read
        (.storage (cells base noQuantum I index).toCStorageRef)).toFin.val =
      (basis (readout base noQuantum I index).wire).val := by
  have actual := Circuit.writeMeasurementBasis_read (readouts base noQuantum I)
    (nativeECDLP_readouts_nodup base noQuantum I) (readout base noQuantum I index)
    (List.mem_ofFn.mpr ⟨index, rfl⟩) store basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  rw [readout_value] at numeric
  exact numeric

private theorem wire_value (basis : (context base noQuantum I).register.Index)
    (index : Fin (Layout.totalQubits I)) :
    (basis (wireEquiv I (nativeECDLP_context_wires base noQuantum I) index)).val =
      ((qubitLayout I).binaryIndexEquiv.symm
        (basisEquiv I (nativeECDLP_context_wires base noQuantum I) basis) index).val := by
  let correspondence := Execution.basisOfEqualWires (bankLayout I)
    (context base noQuantum I).quantumLayout
    (layoutWires I (nativeECDLP_context_wires base noQuantum I))
  have value := Execution.basisOfEqualWires_value (bankLayout I)
    (context base noQuantum I).quantumLayout
    (layoutWires I (nativeECDLP_context_wires base noQuantum I))
    (correspondence.symm basis) index
  change (correspondence (correspondence.symm basis)
    (wireEquiv I (nativeECDLP_context_wires base noQuantum I) index)).val = _ at value
  rw [Equiv.apply_symm_apply] at value
  have inverse := Equiv.symm_apply_apply (qubitLayout I).binaryIndexEquiv
    (correspondence.symm basis)
  exact value.trans (congrArg
    (fun source : (qubitLayout I).toQuantumLayout.Basis => (source index).val) inverse).symm

/-- The stored exponent bits have exactly the original terminal measurement's significance. -/
theorem nativeECDLP_measured_bit (store : Store (context base noQuantum I))
    (basis : (context base noQuantum I).register.Index) (index : Fin (sampleWidth I)) :
    decide ((((Circuit.writeMeasurementPath (readouts base noQuantum I) store
      (Circuit.measurementBasisPath (readouts base noQuantum I) basis)).read
        (.storage (cells base noQuantum I index).toCStorageRef)).toFin.val) = 1) =
      (terminalMeasurement I).readout
        (basisEquiv I (nativeECDLP_context_wires base noQuantum I) basis) index := by
  rw [nativeECDLP_measured_cell]
  let source := (terminalMeasurement I).logical_idx index
  let binary := basisEquiv I (nativeECDLP_context_wires base noQuantum I) basis
  have finiteValue := wire_value base noQuantum I basis source
  have bit := (qubitLayout I).binaryIndexEquiv_bit
    ((qubitLayout I).binaryIndexEquiv.symm binary) source
  rw [Equiv.apply_symm_apply] at bit
  have converted (value : Fin 2) : decide (value.val = 1) = finTwoEquiv value := by
    fin_cases value <;> rfl
  calc
    _ = finTwoEquiv ((qubitLayout I).binaryIndexEquiv.symm binary source) :=
      (congrArg (fun value => decide (value = 1)) finiteValue).trans (converted _)
    _ = binary.val.testBit source.rev.val := bit.symm
    _ = _ := by
      change binary.val.testBit source.rev.val =
        binary.val.testBit (Layout.totalQubits I - 1 - source.val)
      congr 1
      simp only [Fin.rev]
      omega

/-- The actual measurement writes preserve every structural operand from before allocation. -/
theorem nativeECDLP_measured_input {shape : CShape} (input : CInputRef base shape)
    (store : Store (context base noQuantum I)) (basis : (context base noQuantum I).register.Index) :
    (Circuit.writeMeasurementPath (readouts base noQuantum I) store
      (Circuit.measurementBasisPath (readouts base noQuantum I) basis)).read
        (liftInput base noQuantum I input) = store.read (liftInput base noQuantum I input) := by
  apply Circuit.writeMeasurementPath_read_input
  intro item present
  obtain ⟨position, rfl⟩ := List.mem_ofFn.mp present
  rw [readout_key]
  exact MeasurementCells.reference_not_mem_liftInput 2 _ (sampleWidth I) position

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
