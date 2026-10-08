/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Measurement
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Execution.FiniteReadout
import all QuantumAlg.Core.Execution.Measurement.Readout

/-!
# Actual declared measurement bits and packed result

The physical phase-wire measurements and paid bit packing retain the
original Shor outcome order on the declared Shor program.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem outcomeLayoutWires {ctx : RuntimeCtx .quantum} (N : Nat)
    (sameWires : ctx.quantumWires = (layout N).wires) :
    (layout N).wires = ctx.quantumLayout.wires :=
  (ctx.quantumLayout_wires.trans sameWires).symm

variable (base : RuntimeCtx .quantum) (N : Nat) (sameWires : base.quantumWires = (layout N).wires)

private theorem readout_key (index : Fin (phaseBits N)) :
    (readout base N sameWires index).output.key = (Storage.cells base N index).key :=
  FiniteReadout.transported_key
    (shorDeclared_context_qubits N ((Storage.quantumWires base N).trans sameWires) _)
    (Storage.cells base N index)

private theorem readout_value (index : Fin (phaseBits N))
    (store : Store (Storage.context base N)) :
    (store.read (.storage (readout base N sameWires index).output.toCStorageRef)).toFin.val =
      (store.read (.storage (Storage.cells base N index).toCStorageRef)).toFin.val :=
  FiniteReadout.transported_read_value
    (shorDeclared_context_qubits N ((Storage.quantumWires base N).trans sameWires) _)
    (Storage.cells base N index) store

private theorem readouts_nodup :
    ((readouts base N sameWires).map fun item => item.output.key).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right same
  have keys := (readout_key base N sameWires left).symm.trans
    (same.trans (readout_key base N sameWires right))
  exact MeasurementCells.reference_key_injective _ _ _ keys

private theorem measured_cell (input : Input N) (store : Store (Storage.context base N))
    (basis : (Storage.context base N).register.Index)
    (index : Fin (phaseBits N)) :
    ((measuredStore base N input sameWires store basis).read
        (.storage (Storage.cells base N index).toCStorageRef)).toFin.val =
      (basis (readout base N sameWires index).wire).val := by
  have actual := Circuit.writeMeasurementBasis_read
    (gates := AlgorithmGate.model)
    (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
    (operations := BitWord.model)
    (services := ClassicalOracleModel.empty)
    (readouts base N sameWires)
    (readouts_nodup base N sameWires) (readout base N sameWires index)
    (List.mem_ofFn.mpr ⟨index, rfl⟩) store basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  rw [readout_value] at numeric
  exact numeric

private theorem wire_value (basis : (Storage.context base N).register.Index)
    (index : Fin (bankQubits N)) :
    (basis (wireEquiv N ((Storage.quantumWires base N).trans sameWires) index)).val =
      ((OrderFinding.Native.sourceLayout (phaseBits N) (modulusBits N)).binaryIndexEquiv.symm
        (basisEquiv N ((Storage.quantumWires base N).trans sameWires) basis)
        index).val := by
  let correspondence := Execution.basisOfEqualWires (layout N)
    (Storage.context base N).quantumLayout
    (outcomeLayoutWires N ((Storage.quantumWires base N).trans sameWires))
  have value := Execution.basisOfEqualWires_value (layout N)
    (Storage.context base N).quantumLayout
    (outcomeLayoutWires N ((Storage.quantumWires base N).trans sameWires))
    (correspondence.symm basis) index
  change (correspondence (correspondence.symm basis)
    (wireEquiv N ((Storage.quantumWires base N).trans sameWires)
      index)).val = _ at value
  rw [Equiv.apply_symm_apply] at value
  have inverse := Equiv.symm_apply_apply
    (OrderFinding.Native.sourceLayout (phaseBits N) (modulusBits N)).binaryIndexEquiv
    (correspondence.symm basis)
  exact value.trans (congrArg
    (fun source :
      (OrderFinding.Native.sourceLayout (phaseBits N) (modulusBits N)).toQuantumLayout.Basis =>
      (source index).val)
    inverse).symm

private theorem measured_bit (basis : (Storage.context base N).register.Index)
    (index : Fin (phaseBits N)) :
    decide ((basis (readout base N sameWires index).wire).val = 1) =
      (OrderFinding.Native.measurement (phaseBits N) (modulusBits N)).readout
        (basisEquiv N ((Storage.quantumWires base N).trans sameWires) basis) index := by
  let source := (OrderFinding.Native.measurement (phaseBits N) (modulusBits N)).logical_idx index
  let binary := basisEquiv N ((Storage.quantumWires base N).trans sameWires) basis
  have finiteValue := wire_value base N sameWires basis source
  have bit := (OrderFinding.Native.sourceLayout (phaseBits N) (modulusBits N)).binaryIndexEquiv_bit
    ((OrderFinding.Native.sourceLayout (phaseBits N) (modulusBits N)).binaryIndexEquiv.symm
      binary) source
  have inverse := congrArg
    (fun label : Fin (2 ^ (phaseBits N + modulusBits N)) =>
      label.val.testBit source.rev.val)
    (Equiv.apply_symm_apply
      (OrderFinding.Native.sourceLayout (phaseBits N) (modulusBits N)).binaryIndexEquiv
      binary)
  have converted (value : Fin 2) : decide (value.val = 1) = finTwoEquiv value := by
    fin_cases value <;> rfl
  calc
    _ = finTwoEquiv
        ((OrderFinding.Native.sourceLayout (phaseBits N) (modulusBits N)).binaryIndexEquiv.symm
          binary source) :=
      (congrArg (fun value => decide (value = 1)) finiteValue).trans (converted _)
    _ = binary.val.testBit source.rev.val := bit.symm.trans inverse
    _ = _ := by
      change binary.val.testBit source.rev.val =
        binary.val.testBit (bankQubits N - 1 - source.val)
      congr 1
      simp only [Fin.rev, bankQubits]
      omega

/-- The same actual writes and final packing compute precisely the original phase outcome. -/
theorem packed_output (input : Input N) (store : Store (Storage.context base N))
    (basis : (Storage.context base N).register.Index) :
    ((measuredStore base N input sameWires store basis).applyOp
        (packing base N)).read
          (.storage (Storage.resultRef base N).toCStorageRef) =
      CShape.Value.bits ((OrderFinding.Native.measurement (phaseBits N) (modulusBits N)).readout
        (basisEquiv N ((Storage.quantumWires base N).trans sameWires) basis)) := by
  refine (Store.read_applyOp_output _ (packing base N)).trans ?_
  change CShape.Value.bits (fun index => decide
    (((measuredStore base N input sameWires store basis).read
        (.storage (Storage.cells base N index).toCStorageRef)).toFin.val = 1)) = _
  apply congrArg CShape.Value.bits
  funext index
  rw [measured_cell base N sameWires input]
  exact measured_bit base N sameWires basis index



end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
