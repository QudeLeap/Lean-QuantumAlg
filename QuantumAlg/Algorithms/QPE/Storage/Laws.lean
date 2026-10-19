/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Algorithms.QPE.Context
import all QuantumAlg.Algorithms.QPE.Storage
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Measure.Distribution

/-!
# Actual phase measurements and packed output values

Distinct finite result cells record the leading phase-wire values. The real
packing instruction converts those same stored values to the mathematical
phase readout in canonical order, while retaining the unmeasured source.
-/

namespace QuantumAlg.QuantumPhaseEstimation

noncomputable section

open QuantumAlg.Execution

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

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

lemma phaseReadout_key (t n : Nat) (index : Fin t) :
    (phaseReadout t n index).output.key =
      (MeasurementCells.reference (resultContext t n) 2 t index).key :=
  transported_key (phaseWire_dimension t n index) _

lemma phaseReadout_read_value (t n : Nat) (index : Fin t) (store : Store (post t n)) :
    (store.read (.storage (phaseReadout t n index).output.toCStorageRef)).toFin.val =
      (store.read (.storage
        (MeasurementCells.reference (resultContext t n) 2 t index).toCStorageRef)).toFin.val :=
  transported_read_value (phaseWire_dimension t n index) _ store

lemma readouts_keys_nodup (t n : Nat) :
    ((readouts t n).map (fun item => item.output.key)).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right same
  apply MeasurementCells.reference_key_injective (resultContext t n) 2 t
  exact (phaseReadout_key t n left).symm.trans (same.trans (phaseReadout_key t n right))

/-- The typed actual measurement writes the original finite value into its own retained cell. -/
lemma measuredCell_value (t n : Nat) (store : Store (post t n))
    (basis : (post t n).register.Index) (index : Fin t) :
    ((Circuit.writeMeasurementPath (allowAllocation := true) (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) (readouts t n) store
      (Circuit.measurementBasisPath (allowAllocation := true) (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services) (readouts t n) basis)).read
        (.storage
          (MeasurementCells.reference (resultContext t n) 2 t index).toCStorageRef)).toFin.val =
      (basis (phaseWire t n index)).val := by
  have actual := Circuit.writeMeasurementBasis_read (allowAllocation := true)
    (gates := gates) (oracles := oracles)
    (operations := operations) (services := services) (readouts t n) (readouts_keys_nodup t n)
    (phaseReadout t n index) (List.mem_ofFn.mpr ⟨index, rfl⟩) store basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  rw [phaseReadout_read_value] at numeric
  exact numeric

/-- The canonical binary basis has exactly the same actual phase-wire values. -/
lemma phaseWire_value (t n : Nat) (basis : (post t n).register.Index) (index : Fin t) :
    (basis (phaseWire t n index)).val =
      ((qpeLayout t n).binaryIndexEquiv.symm (outputBasisEquiv t n basis)
        (Fin.castAdd n index)).val := by
  let oldBasis := (MeasurementCells.basisEquiv (resultContext t n) 2 t).symm basis
  have cells := MeasurementCells.basisEquiv_value (resultContext t n) 2 t oldBasis
    (preparedWire t n (Fin.castAdd n index))
  have prepared := preparedLayoutEquiv_value t n ((preparedLayoutEquiv t n).symm oldBasis)
    (Fin.castAdd n index)
  rw [Equiv.apply_symm_apply] at prepared
  change (MeasurementCells.basisEquiv (resultContext t n) 2 t
    ((MeasurementCells.basisEquiv (resultContext t n) 2 t).symm basis)
      (phaseWire t n index)).val = _ at cells
  rw [Equiv.apply_symm_apply] at cells
  change (basis (phaseWire t n index)).val =
    ((qpeLayout t n).binaryIndexEquiv.symm
      ((qpeLayout t n).binaryIndexEquiv ((preparedLayoutEquiv t n).symm oldBasis))
        (Fin.castAdd n index)).val
  rw [Equiv.symm_apply_apply]
  exact cells.trans prepared

private lemma finiteBit_encoding (value : Fin 2) :
    decide (value.val = 1) = finTwoEquiv value := by
  fin_cases value <;> rfl

/-- Boolean packing uses the same big-endian wire order as the mathematical readout. -/
lemma phaseWire_bit (t n : Nat) (basis : (post t n).register.Index) (index : Fin t) :
    decide ((basis (phaseWire t n index)).val = 1) =
      (qpeMeasurement t n).readout (outputBasisEquiv t n basis) index := by
  calc
    _ = finTwoEquiv
        ((qpeLayout t n).binaryIndexEquiv.symm (outputBasisEquiv t n basis)
          (Fin.castAdd n index)) :=
      (congrArg (fun value => decide (value = 1)) (phaseWire_value t n basis index)).trans
        (finiteBit_encoding _)
    _ = _ := by
      have bit := (qpeLayout t n).binaryIndexEquiv_bit
        ((qpeLayout t n).binaryIndexEquiv.symm (outputBasisEquiv t n basis)) (Fin.castAdd n index)
      rw [Equiv.apply_symm_apply] at bit
      change _ = (outputBasisEquiv t n basis).val.testBit (t + n - 1 - index.val)
      have position : t + n - 1 - index.val = (Fin.castAdd n index).rev.val := by
        have castValue : (Fin.castAdd n index).val = index.val := rfl
        simp only [Fin.rev]
        omega
      rw [position]
      exact bit.symm

/-- The real packing opcode converts the actual retained outcomes into
the original phase readout. -/
lemma packing_measured_value (t n : Nat) (store : Store (post t n))
    (basis : (post t n).register.Index) :
    (packing t n).eval ((Circuit.writeMeasurementPath (allowAllocation := true)
      (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) (readouts t n) store
      (Circuit.measurementBasisPath (allowAllocation := true) (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services) (readouts t n) basis)).read
        (MeasurementCells.input (resultContext t n) 2 t)) =
      CShape.Value.bits ((qpeMeasurement t n).readout (outputBasisEquiv t n basis)) := by
  change CShape.Value.bits (fun index => decide
    (((Circuit.writeMeasurementPath (allowAllocation := true) (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) (readouts t n) store
      (Circuit.measurementBasisPath (allowAllocation := true) (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services) (readouts t n) basis)).read
        (.storage
          (MeasurementCells.reference (resultContext t n) 2 t index).toCStorageRef)).toFin.val =
          1)) = _
  apply congrArg CShape.Value.bits
  funext index
  rw [measuredCell_value]
  exact phaseWire_bit t n basis index

end

end QuantumAlg.QuantumPhaseEstimation
