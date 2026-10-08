/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Measurement
import all QuantumAlg.Core.Execution.FiniteReadout
import all QuantumAlg.Core.Execution.Measurement.Readout

/-!
# Actual declared measurement bits and packed result

The physical exponent-wire measurements and paid bit packing retain the
original short-DLP outcome order on the declared EH program.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private theorem readout_key (index : Fin (measurementBits N)) :
    (readout base noQuantum N index).output.key = (Native.cells base noQuantum N index).key :=
  FiniteReadout.transported_key
    (Native.nativeOracle_context_qubits N (Native.nativeOracle_context_wires base noQuantum N) _)
    (Native.cells base noQuantum N index)

private theorem readout_value (index : Fin (measurementBits N))
    (store : Store (Native.context base noQuantum N)) :
    (store.read (.storage (readout base noQuantum N index).output.toCStorageRef)).toFin.val =
      (store.read (.storage (Native.cells base noQuantum N index).toCStorageRef)).toFin.val :=
  FiniteReadout.transported_read_value
    (Native.nativeOracle_context_qubits N (Native.nativeOracle_context_wires base noQuantum N) _)
    (Native.cells base noQuantum N index) store

private theorem readouts_nodup :
    ((readouts base noQuantum N).map fun item => item.output.key).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right same
  have keys := (readout_key base noQuantum N left).symm.trans
    (same.trans (readout_key base noQuantum N right))
  exact MeasurementCells.reference_key_injective _ _ _ keys

private theorem measured_cell (input : Input N) (store : Store (Native.context base noQuantum N))
    (basis : (Native.context base noQuantum N).register.Index)
    (index : Fin (measurementBits N)) :
    ((measuredStore base noQuantum N input store basis).read
        (.storage (Native.cells base noQuantum N index).toCStorageRef)).toFin.val =
      (basis (readout base noQuantum N index).wire).val := by
  have actual := Circuit.writeMeasurementBasis_read
    (gates := AlgorithmGate.model)
    (oracles := ShortDLP.declaredModel (Native.encoding input))
    (operations := BitWord.model)
    (services := ClassicalOracleModel.empty)
    (readouts base noQuantum N)
    (readouts_nodup base noQuantum N) (readout base noQuantum N index)
    (List.mem_ofFn.mpr ⟨index, rfl⟩) store basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  rw [readout_value] at numeric
  exact numeric

private theorem wire_value (basis : (Native.context base noQuantum N).register.Index)
    (index : Fin (ShortDLP.totalQubits (Native.parameters N))) :
    (basis (Native.wireEquiv N (Native.nativeOracle_context_wires base noQuantum N) index)).val =
      ((ShortDLP.layout (Native.parameters N)).binaryIndexEquiv.symm
        (Native.basisEquiv N (Native.nativeOracle_context_wires base noQuantum N) basis)
        index).val := by
  let correspondence := Execution.basisOfEqualWires (Native.layout N)
    (Native.context base noQuantum N).quantumLayout
    (Native.layoutWires N (Native.nativeOracle_context_wires base noQuantum N))
  have value := Execution.basisOfEqualWires_value (Native.layout N)
    (Native.context base noQuantum N).quantumLayout
    (Native.layoutWires N (Native.nativeOracle_context_wires base noQuantum N))
    (correspondence.symm basis) index
  change (correspondence (correspondence.symm basis)
    (Native.wireEquiv N (Native.nativeOracle_context_wires base noQuantum N)
      index)).val = _ at value
  rw [Equiv.apply_symm_apply] at value
  have inverse := Equiv.symm_apply_apply (ShortDLP.layout (Native.parameters N)).binaryIndexEquiv
    (correspondence.symm basis)
  exact value.trans (congrArg
    (fun source : (ShortDLP.layout (Native.parameters N)).toQuantumLayout.Basis =>
      (source index).val)
    inverse).symm

private theorem measured_bit (basis : (Native.context base noQuantum N).register.Index)
    (index : Fin (measurementBits N)) :
    decide ((basis (readout base noQuantum N index).wire).val = 1) =
      (ShortDLP.measurement (Native.parameters N)).readout
        (Native.basisEquiv N (Native.nativeOracle_context_wires base noQuantum N) basis) index := by
  let source := (ShortDLP.measurement (Native.parameters N)).logical_idx index
  let binary := Native.basisEquiv N (Native.nativeOracle_context_wires base noQuantum N) basis
  have finiteValue := wire_value base noQuantum N basis source
  have bit := (ShortDLP.layout (Native.parameters N)).binaryIndexEquiv_bit
    ((ShortDLP.layout (Native.parameters N)).binaryIndexEquiv.symm binary) source
  rw [Equiv.apply_symm_apply] at bit
  have converted (value : Fin 2) : decide (value.val = 1) = finTwoEquiv value := by
    fin_cases value <;> rfl
  calc
    _ = finTwoEquiv ((ShortDLP.layout (Native.parameters N)).binaryIndexEquiv.symm binary source) :=
      (congrArg (fun value => decide (value = 1)) finiteValue).trans (converted _)
    _ = binary.val.testBit source.rev.val := bit.symm
    _ = _ := by
      change binary.val.testBit source.rev.val =
        binary.val.testBit (ShortDLP.totalQubits (Native.parameters N) - 1 - source.val)
      congr 1
      simp only [Fin.rev]
      omega

/-- The same actual writes and final packing compute precisely the original exponent outcome. -/
theorem packed_output (input : Input N) (store : Store (Native.context base noQuantum N))
    (basis : (Native.context base noQuantum N).register.Index) :
    ((measuredStore base noQuantum N input store basis).applyOp
        (packing base noQuantum N)).read
          (.storage (Native.resultRef base noQuantum N).toCStorageRef) =
      CShape.Value.bits ((ShortDLP.measurement (Native.parameters N)).readout
        (Native.basisEquiv N (Native.nativeOracle_context_wires base noQuantum N) basis)) := by
  refine (Store.read_applyOp_output _ (packing base noQuantum N)).trans ?_
  change CShape.Value.bits (fun index => decide
    (((measuredStore base noQuantum N input store basis).read
        (.storage (Native.cells base noQuantum N index).toCStorageRef)).toFin.val = 1)) = _
  apply congrArg CShape.Value.bits
  funext index
  rw [measured_cell base noQuantum N input]
  exact measured_bit base noQuantum N basis index



end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared
