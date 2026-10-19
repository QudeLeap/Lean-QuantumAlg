/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace

import all QuantumAlg.Algorithms.Grover.Construction
import all QuantumAlg.Algorithms.Grover.Context
import all QuantumAlg.Algorithms.Grover.Storage
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Measure.Distribution

/-!
# Grover's actual Z writes and the canonical packed index

Each finite measurement cell has its own distinct key. Actual writes and
subsequent reads preserve the measured wire values, and the closed packing
opcode uses exactly their original big-endian order. The mathematical
full-register decoder therefore receives the actual bits from execution.

-/

namespace QuantumAlg.GroverSearch

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

open QuantumAlg.Execution

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}

private lemma transported_key {ctx : RuntimeCtx .quantum} {actual intended : ℕ+}
    (same : actual = intended) (ref : CWriteRef ctx (.finite intended)) :
    (Eq.mpr (congrArg (fun dimension => CWriteRef ctx (.finite dimension)) same) ref).key =
      ref.key := by
  cases same
  rfl

private lemma transported_read_value {ctx : RuntimeCtx .quantum} {actual intended : ℕ+}
    (same : actual = intended) (ref : CWriteRef ctx (.finite intended)) (store : Store ctx) :
    (store.read (.storage
      (Eq.mpr (congrArg (fun dimension => CWriteRef ctx (.finite dimension)) same)
        ref).toCStorageRef)).toFin.val = (store.read (.storage ref.toCStorageRef)).toFin.val := by
  cases same
  rfl

lemma queryReadout_key (n k : Nat) (index : Fin n) :
    (queryReadout n k index).output.key =
      (MeasurementCells.reference (resultContext n k) 2 n index).key :=
  transported_key (queryWire_dimension n k index) _

lemma queryReadout_read_value (n k : Nat) (index : Fin n) (store : Store (post n k)) :
    (store.read (.storage (queryReadout n k index).output.toCStorageRef)).toFin.val =
      (store.read (.storage
        (MeasurementCells.reference (resultContext n k) 2 n index).toCStorageRef)).toFin.val :=
  transported_read_value (queryWire_dimension n k index) _ store

lemma readouts_keys_nodup (n k : Nat) :
    ((readouts n k).map (fun item => item.output.key)).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right same
  apply MeasurementCells.reference_key_injective (resultContext n k) 2 n
  exact (queryReadout_key n k left).symm.trans (same.trans (queryReadout_key n k right))

/-- The typed actual measurement writes the original finite value into its own retained cell. -/
lemma measuredCell_value (n k : Nat) (store : Store (post n k))
    (basis : (post n k).register.Index) (index : Fin n) :
    ((Circuit.writeMeasurementPath (allowAllocation := true) (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) (readouts n k) store
      (Circuit.measurementBasisPath (allowAllocation := true) (readouts n k) basis)).read
        (.storage
          (MeasurementCells.reference (resultContext n k) 2 n index).toCStorageRef)).toFin.val =
      (basis (queryWire n k index)).val := by
  have actual := Circuit.writeMeasurementBasis_read (allowAllocation := true)
    (gates := gates) (oracles := oracles)
      (operations := operations) (services := classicalOracles) (readouts n k)
    (readouts_keys_nodup n k)
    (queryReadout n k index) (List.mem_ofFn.mpr ⟨index, rfl⟩) store basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  rw [queryReadout_read_value] at numeric
  exact numeric

/-- The decoded complete binary basis has exactly the same measured source-wire values. -/
lemma queryWire_value (n k : Nat) (basis : (post n k).register.Index) (index : Fin n) :
    (basis (queryWire n k index)).val =
      ((layout (totalQubits n k)).binaryIndexEquiv.symm
        (outputBasisEquiv n k basis) (Fin.castAdd (helperWidth n k) index)).val := by
  let oldBasis := (MeasurementCells.basisEquiv (resultContext n k) 2 n).symm basis
  have cells := MeasurementCells.basisEquiv_value (resultContext n k) 2 n oldBasis
    (preparedWire (totalQubits n k) (Fin.castAdd (helperWidth n k) index))
  have prepared := preparedLayoutEquiv_value (totalQubits n k)
    ((preparedLayoutEquiv (totalQubits n k)).symm oldBasis)
    (Fin.castAdd (helperWidth n k) index)
  rw [Equiv.apply_symm_apply] at prepared
  change (MeasurementCells.basisEquiv (resultContext n k) 2 n
    ((MeasurementCells.basisEquiv (resultContext n k) 2 n).symm basis)
      (queryWire n k index)).val = _ at cells
  rw [Equiv.apply_symm_apply] at cells
  change (basis (queryWire n k index)).val =
    ((layout (totalQubits n k)).binaryIndexEquiv.symm
      ((layout (totalQubits n k)).binaryIndexEquiv
        ((preparedLayoutEquiv (totalQubits n k)).symm oldBasis))
        (Fin.castAdd (helperWidth n k) index)).val
  rw [Equiv.symm_apply_apply]
  exact cells.trans prepared

private lemma finiteBit_encoding (value : Fin 2) :
    decide (value.val = 1) = finTwoEquiv value := by
  fin_cases value <;> rfl

/-- Boolean packing uses the original source order and never reads the retained work suffix. -/
lemma queryWire_bit (n k : Nat) (basis : (post n k).register.Index) (index : Fin n) :
    decide ((basis (queryWire n k index)).val = 1) =
      (zMeasure (layout n)).readout (outputSource n k basis) index := by
  calc
    _ = finTwoEquiv
        ((layout (totalQubits n k)).binaryIndexEquiv.symm
          (outputBasisEquiv n k basis) (Fin.castAdd (helperWidth n k) index)) :=
      (congrArg (fun value => decide (value = 1)) (queryWire_value n k basis index)).trans
        (finiteBit_encoding _)
    _ = (outputBasisEquiv n k basis).val.testBit
        (helperWidth n k + index.rev.val) := by
      have bit := (layout (totalQubits n k)).binaryIndexEquiv_bit
        ((layout (totalQubits n k)).binaryIndexEquiv.symm
          (outputBasisEquiv n k basis)) (Fin.castAdd (helperWidth n k) index)
      rw [Equiv.apply_symm_apply] at bit
      have position : (Fin.castAdd (helperWidth n k) index).rev.val =
          helperWidth n k + index.rev.val := by
        have castValue : (Fin.castAdd (helperWidth n k) index).val = index.val := rfl
        simp only [Fin.rev]
        omega
      exact bit.symm.trans (congrArg _ position)
    _ = (outputSource n k basis).val.testBit index.rev.val := by
      let pair := (prodEquiv (m := n) (n := helperWidth n k)).symm
        (outputBasisEquiv n k basis)
      have encoded := prodEquiv_testBit_left pair.1 pair.2 index.rev
      dsimp only [pair] at encoded
      rw [Prod.mk.eta, Equiv.apply_symm_apply] at encoded
      exact encoded
    _ = _ := by
      change _ = (outputSource n k basis).val.testBit (n - 1 - index.val)
      have position : index.rev.val = n - 1 - index.val := by
        simp only [Fin.rev]
        omega
      rw [position]

/-- The real packing opcode converts the actual retained outcomes into
the original query readout. -/
lemma packing_measured_value (n k : Nat) (store : Store (post n k))
    (basis : (post n k).register.Index) :
    (packing n k).eval ((Circuit.writeMeasurementPath (allowAllocation := true)
      (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) (readouts n k) store
      (Circuit.measurementBasisPath (allowAllocation := true) (readouts n k) basis)).read
        (MeasurementCells.input (resultContext n k) 2 n)) =
      CShape.Value.bits ((zMeasure (layout n)).readout (outputSource n k basis)) := by
  change CShape.Value.bits (fun index => decide
    (((Circuit.writeMeasurementPath (allowAllocation := true) (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) (readouts n k) store
      (Circuit.measurementBasisPath (allowAllocation := true) (readouts n k) basis)).read
        (.storage
          (MeasurementCells.reference (resultContext n k) 2 n index).toCStorageRef)).toFin.val =
          1)) = _
  apply congrArg CShape.Value.bits
  funext index
  rw [measuredCell_value]
  exact queryWire_bit n k basis index

end

end QuantumAlg.GroverSearch
