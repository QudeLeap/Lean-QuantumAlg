/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.AccessCircuit
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Context
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Storage
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Measure.Distribution

import all QuantumAlg.Core.Execution.FiniteReadout

/-!
# Actual stored phase readout with a retained classical input frame

The same finite measurement cells and physical phase wires determine the
stored packed output. These equations are independent of the input frame's
classical values and preserve the original source basis convention.
-/

namespace QuantumAlg.OrderFinding.Sampling.Framed

noncomputable section

open QuantumAlg.Execution

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

theorem phaseReadout_key (t n : Nat) (index : Fin t) :
    (phaseReadout ctx noQuantum t n index).output.key =
      (MeasurementCells.reference (resultContext ctx noQuantum t n) 2 t index).key :=
  FiniteReadout.transported_key (phaseWire_dimension ctx noQuantum t n index) _

theorem phaseReadout_read_value (t n : Nat) (index : Fin t)
    (store : Store (post ctx noQuantum t n)) :
    (store.read (.storage (phaseReadout ctx noQuantum t n index).output.toCStorageRef)).toFin.val =
      (store.read (.storage
        (MeasurementCells.reference
          (resultContext ctx noQuantum t n) 2 t index).toCStorageRef)).toFin.val :=
  FiniteReadout.transported_read_value (phaseWire_dimension ctx noQuantum t n index) _ store

theorem readouts_keys_nodup (t n : Nat) :
    ((readouts ctx noQuantum t n).map (fun item => item.output.key)).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right same
  apply MeasurementCells.reference_key_injective (resultContext ctx noQuantum t n) 2 t
  exact (phaseReadout_key ctx noQuantum t n left).symm.trans
    (same.trans (phaseReadout_key ctx noQuantum t n right))

/-- The typed actual measurement writes the original finite value into its own retained cell. -/
theorem measuredCell_value (t n : Nat) (store : Store (post ctx noQuantum t n))
    (basis : (post ctx noQuantum t n).register.Index) (index : Fin t) :
    ((Circuit.writeMeasurementPath (readouts ctx noQuantum t n) store
      (Circuit.measurementBasisPath (readouts ctx noQuantum t n) basis)).read
        (.storage
          (MeasurementCells.reference
            (resultContext ctx noQuantum t n) 2 t index).toCStorageRef)).toFin.val =
      (basis (phaseWire ctx noQuantum t n index)).val := by
  have actual := Circuit.writeMeasurementBasis_read (readouts ctx noQuantum t n)
    (readouts_keys_nodup ctx noQuantum t n)
    (phaseReadout ctx noQuantum t n index) (List.mem_ofFn.mpr ⟨index, rfl⟩) store basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  rw [phaseReadout_read_value] at numeric
  exact numeric

/-- The canonical binary basis has exactly the same actual phase-wire values. -/
theorem phaseWire_value (t n : Nat) (basis : (post ctx noQuantum t n).register.Index)
    (index : Fin t) :
    (basis (phaseWire ctx noQuantum t n index)).val =
      ((sourceLayout t n).binaryIndexEquiv.symm
        (outputBasisEquiv ctx noQuantum t n basis)
        (Fin.castAdd n index)).val := by
  let oldBasis := (MeasurementCells.basisEquiv (resultContext ctx noQuantum t n) 2 t).symm basis
  have cells := MeasurementCells.basisEquiv_value (resultContext ctx noQuantum t n) 2 t oldBasis
    (preparedWire ctx noQuantum t n (Fin.castAdd n index))
  have prepared := preparedLayoutEquiv_value ctx noQuantum t n
    ((preparedLayoutEquiv ctx noQuantum t n).symm oldBasis)
    (Fin.castAdd n index)
  rw [Equiv.apply_symm_apply] at prepared
  change (MeasurementCells.basisEquiv (resultContext ctx noQuantum t n) 2 t
    ((MeasurementCells.basisEquiv (resultContext ctx noQuantum t n) 2 t).symm basis)
      (phaseWire ctx noQuantum t n index)).val = _ at cells
  rw [Equiv.apply_symm_apply] at cells
  change (basis (phaseWire ctx noQuantum t n index)).val =
    ((sourceLayout t n).binaryIndexEquiv.symm
      ((sourceLayout t n).binaryIndexEquiv
        ((preparedLayoutEquiv ctx noQuantum t n).symm oldBasis))
        (Fin.castAdd n index)).val
  rw [Equiv.symm_apply_apply]
  exact cells.trans prepared

private theorem finiteBit_encoding (value : Fin 2) :
    decide (value.val = 1) = finTwoEquiv value := by
  fin_cases value <;> rfl

/-- Boolean packing uses the same big-endian wire order as the mathematical readout. -/
theorem phaseWire_bit (t n : Nat) (basis : (post ctx noQuantum t n).register.Index)
    (index : Fin t) :
    decide ((basis (phaseWire ctx noQuantum t n index)).val = 1) =
      (measurement t n).readout
        (outputBasisEquiv ctx noQuantum t n basis) index := by
  calc
    _ = finTwoEquiv
        ((sourceLayout t n).binaryIndexEquiv.symm
        (outputBasisEquiv ctx noQuantum t n basis)
          (Fin.castAdd n index)) :=
      (congrArg (fun value => decide (value = 1))
        (phaseWire_value ctx noQuantum t n basis index)).trans
        (finiteBit_encoding _)
    _ = _ := by
      have bit := (sourceLayout t n).binaryIndexEquiv_bit
        ((sourceLayout t n).binaryIndexEquiv.symm
        (outputBasisEquiv ctx noQuantum t n basis))
        (Fin.castAdd n index)
      rw [Equiv.apply_symm_apply] at bit
      change _ = (outputBasisEquiv ctx noQuantum t n basis).val.testBit
        (t + n - 1 - index.val)
      have position : t + n - 1 - index.val =
          (Fin.castAdd n index).rev.val := by
        have castValue : (Fin.castAdd n index).val = index.val := rfl
        simp only [Fin.rev]
        omega
      rw [position]
      exact bit.symm

/-- The real packing opcode converts the actual retained outcomes into
the original phase readout. -/
theorem packing_measured_value (t n : Nat) (store : Store (post ctx noQuantum t n))
    (basis : (post ctx noQuantum t n).register.Index) :
    (packing ctx noQuantum t n).eval
      ((Circuit.writeMeasurementPath (readouts ctx noQuantum t n) store
      (Circuit.measurementBasisPath (readouts ctx noQuantum t n) basis)).read
        (MeasurementCells.input (resultContext ctx noQuantum t n) 2 t)) =
      CShape.Value.bits ((measurement t n).readout
        (outputBasisEquiv ctx noQuantum t n basis)) := by
  change CShape.Value.bits (fun index => decide
    (((Circuit.writeMeasurementPath (readouts ctx noQuantum t n) store
      (Circuit.measurementBasisPath (readouts ctx noQuantum t n) basis)).read
        (.storage
          (MeasurementCells.reference
            (resultContext ctx noQuantum t n) 2 t index).toCStorageRef)).toFin.val =
          1)) = _
  apply congrArg CShape.Value.bits
  funext index
  rw [measuredCell_value]
  exact phaseWire_bit ctx noQuantum t n basis index

end

end QuantumAlg.OrderFinding.Sampling.Framed
