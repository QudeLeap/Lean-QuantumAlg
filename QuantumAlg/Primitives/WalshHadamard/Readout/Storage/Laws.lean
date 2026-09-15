/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.WalshHadamard.Readout.Geometry
import all QuantumAlg.Primitives.WalshHadamard.Readout.Context
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Measure.Distribution

/-!
# Actual Walsh-Hadamard query readout measured cells and the packed result

The finite-dimension equality at each query wire transports only its typed
reference. It changes neither the storage key nor the numeric value read
from that cell. Distinct cells therefore retain all actual measured outcomes.
The existing packing instruction writes their original big-endian query
readout, including when the query register is empty.
-/

namespace QuantumAlg.WalshHadamard.Readout

noncomputable section

open QuantumAlg.Execution

private theorem transported_key {ctx : RuntimeCtx .quantum} {actual intended : ℕ+}
    (same : actual = intended) (ref : CWriteRef ctx (.finite intended)) :
    (Eq.mpr (congrArg (fun dimension => CWriteRef ctx (.finite dimension)) same) ref).key =
      ref.key := by
  cases same
  rfl

private theorem transported_read_value {ctx : RuntimeCtx .quantum} {actual intended : ℕ+}
    (same : actual = intended) (ref : CWriteRef ctx (.finite intended)) (store : Store ctx) :
    (store.read (.storage
      (Eq.mpr (congrArg (fun dimension => CWriteRef ctx (.finite dimension)) same)
        ref).toCStorageRef)).toFin.val = (store.read (.storage ref.toCStorageRef)).toFin.val := by
  cases same
  rfl

theorem queryReadout_key (n : Nat) (index : Fin n) :
    (queryReadout n index).output.key =
      (MeasurementCells.reference (resultContext n) 2 n index).key :=
  transported_key (queryWire_dimension n index) _

theorem queryReadout_read_value (n : Nat) (index : Fin n) (store : Store (post n)) :
    (store.read (.storage (queryReadout n index).output.toCStorageRef)).toFin.val =
      (store.read (.storage
        (MeasurementCells.reference (resultContext n) 2 n index).toCStorageRef)).toFin.val :=
  transported_read_value (queryWire_dimension n index) _ store

theorem readouts_keys_nodup (n : Nat) :
    ((readouts n).map (fun item => item.output.key)).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right same
  apply MeasurementCells.reference_key_injective (resultContext n) 2 n
  exact (queryReadout_key n left).symm.trans (same.trans (queryReadout_key n right))

/-- The typed actual measurement writes the original finite value into its own retained cell. -/
theorem measuredCell_value (n : Nat) (store : Store (post n))
    (basis : (post n).register.Index) (index : Fin n) :
    ((Circuit.writeMeasurementPath (readouts n) store
      (Circuit.measurementBasisPath (readouts n) basis)).read
        (.storage
          (MeasurementCells.reference (resultContext n) 2 n index).toCStorageRef)).toFin.val =
      (basis (queryWire n index)).val := by
  have actual := Circuit.writeMeasurementBasis_read (readouts n) (readouts_keys_nodup n)
    (queryReadout n index) (List.mem_ofFn.mpr ⟨index, rfl⟩) store basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  rw [queryReadout_read_value] at numeric
  exact numeric

/-- The decoded old binary basis has exactly the same query-wire values. -/
theorem queryWire_value (n : Nat) (basis : (post n).register.Index) (index : Fin n) :
    (basis (queryWire n index)).val =
      ((layout n).binaryIndexEquiv.symm (outputBasisEquiv n basis) index.castSucc).val := by
  let oldBasis := (MeasurementCells.basisEquiv (resultContext n) 2 n).symm basis
  have cells := MeasurementCells.basisEquiv_value (resultContext n) 2 n oldBasis
    (preparedWire n index.castSucc)
  have prepared := preparedLayoutEquiv_value n ((preparedLayoutEquiv n).symm oldBasis)
    index.castSucc
  rw [Equiv.apply_symm_apply] at prepared
  change (MeasurementCells.basisEquiv (resultContext n) 2 n
    ((MeasurementCells.basisEquiv (resultContext n) 2 n).symm basis)
      (queryWire n index)).val = _ at cells
  rw [Equiv.apply_symm_apply] at cells
  change (basis (queryWire n index)).val =
    ((layout n).binaryIndexEquiv.symm
      ((layout n).binaryIndexEquiv ((preparedLayoutEquiv n).symm oldBasis)) index.castSucc).val
  rw [Equiv.symm_apply_apply]
  exact cells.trans prepared

private theorem finiteBit_encoding (value : Fin 2) :
    decide (value.val = 1) = finTwoEquiv value := by
  fin_cases value <;> rfl

/-- Boolean packing uses the same big-endian wire order as the mathematical readout. -/
theorem queryWire_bit (n : Nat) (basis : (post n).register.Index) (index : Fin n) :
    decide ((basis (queryWire n index)).val = 1) =
      (measurement n).readout (outputBasisEquiv n basis) index := by
  calc
    _ = finTwoEquiv
        ((layout n).binaryIndexEquiv.symm (outputBasisEquiv n basis) index.castSucc) :=
      (congrArg (fun value => decide (value = 1)) (queryWire_value n basis index)).trans
        (finiteBit_encoding _)
    _ = _ := by
      have bit := (layout n).binaryIndexEquiv_bit
        ((layout n).binaryIndexEquiv.symm (outputBasisEquiv n basis)) index.castSucc
      rw [Equiv.apply_symm_apply] at bit
      change _ = (outputBasisEquiv n basis).val.testBit (n + 1 - 1 - index.val)
      have position : n + 1 - 1 - index.val = index.castSucc.rev.val := by
        simp only [Fin.rev, Fin.val_castSucc]
        omega
      rw [position]
      exact bit.symm

/-- The real packing opcode converts the actual retained outcomes into
the original query readout. -/
theorem packing_measured_value (n : Nat) (store : Store (post n))
    (basis : (post n).register.Index) :
    (packing n).eval ((Circuit.writeMeasurementPath (readouts n) store
      (Circuit.measurementBasisPath (readouts n) basis)).read
        (MeasurementCells.input (resultContext n) 2 n)) =
      CShape.Value.bits ((measurement n).readout (outputBasisEquiv n basis)) := by
  change CShape.Value.bits (fun index => decide
    (((Circuit.writeMeasurementPath (readouts n) store
      (Circuit.measurementBasisPath (readouts n) basis)).read
        (.storage
          (MeasurementCells.reference (resultContext n) 2 n index).toCStorageRef)).toFin.val =
          1)) = _
  apply congrArg CShape.Value.bits
  funext index
  rw [measuredCell_value]
  exact queryWire_bit n basis index

end

end QuantumAlg.WalshHadamard.Readout
