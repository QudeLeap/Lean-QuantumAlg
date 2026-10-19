/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Stage.Source
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Head
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Tail
import all QuantumAlg.Core.Measure.Instrument

/-!
# Entries of the literal Fourier head-stage operator

The stored feedback and actual Z projector are full physical diagonals.
Their product with the real H placement therefore has the exact source
phase, the real observed head sector and identity on every tail spectator,
unselected system and external reference coordinate. These equalities come
from the actual native matrices; no lifting or equivalence premise is used.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

noncomputable section

variable {ctx : RuntimeCtx .quantum}

/-- The source phase evaluated on the existing physical tail, with its actual sign. -/
def sourceFeedbackScalar (inverse : Bool) {n : Nat}
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (bit : Fin 2) (basis : ctx.register.Index) : Complex :=
  if bit = 1 then
    (if inverse then star (ω (n + 1) ^ (physicalTailLabel tail tailQubits basis).val)
      else ω (n + 1) ^ (physicalTailLabel tail tailQubits basis).val)
    else 1

/-- Reference extension of the real feedback is diagonal on the complete physical basis. -/
lemma sourceFeedbackReference_diagonal (inverse : Bool) {n : Nat}
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (bit : Fin 2) (Reference : Register) :
    sourceFeedbackReference inverse tail tailQubits bit Reference =
      Matrix.diagonal (fun basis => sourceFeedbackScalar inverse tail tailQubits bit basis.1) := by
  classical
  ext row column
  have equality : row = column ↔ row.1 = column.1 ∧ row.2 = column.2 := Prod.ext_iff
  by_cases physical : row.1 = column.1 <;> by_cases reference : row.2 = column.2 <;>
    simp [sourceFeedbackReference, sourceFeedbackMatrix, sourceFeedbackScalar,
      Matrix.diagonal_apply, equality, physical, reference]

/-- The literal projector and literal feedback multiply the exact real-H entry. -/
lemma nativeStageKraus_physical_entry {environment : OracleModel.empty.Interpretation} (inverse
    : Bool) {n : Nat}
    (head : Fin ctx.systemCount) (headQubit : (ctx.quantumLayout.wire head).dimension = 2)
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (Reference : Register) (outcome : Fin (ctx.quantumLayout.wire head).dimension)
    (row column : (ctx.register.prod Reference).Index) :
    nativeStageKraus (environment := environment) inverse head headQubit tail tailQubits Reference
      outcome row column =
      (sourceFeedbackScalar inverse tail tailQubits
          (outcomeBit head headQubit outcome) row.1 *
        (if row.1 head = outcome then 1 else 0)) *
        (UnitaryOperator.prodTensor
          ((Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp head headQubit).matrix environment)
          (1 : UnitaryOperator Reference)) row column := by
  classical
  rw [nativeStageKraus_eq_source]
  unfold sourceStageKraus
  rw [sourceFeedbackReference_diagonal]
  simp only [ZMeasurement.projector, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul]

/-- The observed head sector is exactly its source-tuple bit, with no casted-value assumption. -/
lemma bankCoordinates_head_outcome_iff {n : Nat}
    (wires : Fin (n + 1) ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (basis : ctx.register.Index) (outcome : Fin (ctx.quantumLayout.wire (wires 0)).dimension) :
    (bankCoordinates wires qubits basis).1.1 = outcomeBit (wires 0) (qubits 0) outcome ↔
      basis (wires 0) = outcome := by
  rw [bankCoordinates_head_value]
  constructor
  · intro same
    exact Fin.ext (congrArg (fun bit : Fin 2 => bit.val) same)
  · intro same
    rw [same]
    rfl

/-- Source-tail coordinates are the actual selected physical coordinates at every width. -/
lemma sourceFeedbackScalar_tail_coordinates (inverse : Bool) {n : Nat}
    (wires : Fin (n + 1) ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (bit : Fin 2) (basis : ctx.register.Index) :
    sourceFeedbackScalar inverse (tailPhysicalWires wires) (fun i => qubits i.succ) bit basis =
      if bit = 1 then
        (if inverse then star (ω (n + 1) ^
            (binaryEquiv n (bankCoordinates wires qubits basis).1.2).val)
          else ω (n + 1) ^ (binaryEquiv n (bankCoordinates wires qubits basis).1.2).val)
        else 1 := by
  unfold sourceFeedbackScalar
  rw [← bankCoordinates_label (tailPhysicalWires wires) (fun i => qubits i.succ) basis,
    tailBankCoordinates_selected wires qubits basis]

/-- The actual head stage keeps all complementary coordinates and the reference explicitly. -/
lemma nativeStageKraus_bank_entry {environment : OracleModel.empty.Interpretation} (inverse :
    Bool) {n : Nat}
    (wires : Fin (n + 1) ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (Reference : Register) (outcome : Fin (ctx.quantumLayout.wire (wires 0)).dimension)
    (row column : (ctx.register.prod Reference).Index) :
    nativeStageKraus (environment := environment) inverse (wires 0) (qubits 0) (tailPhysicalWires
      wires)
        (fun i => qubits i.succ) Reference outcome row column =
      (sourceFeedbackScalar inverse (tailPhysicalWires wires) (fun i => qubits i.succ)
          (outcomeBit (wires 0) (qubits 0) outcome) row.1 *
        (if row.1 (wires 0) = outcome then 1 else 0)) *
        (Gate.HOp (bankCoordinates wires qubits row.1).1.1
            (bankCoordinates wires qubits column.1).1.1 *
          (if (bankCoordinates wires qubits row.1).1.2 =
                (bankCoordinates wires qubits column.1).1.2 ∧
              (bankCoordinates wires qubits row.1).2 =
                (bankCoordinates wires qubits column.1).2 ∧ row.2 = column.2
            then 1 else 0)) := by
  rw [nativeStageKraus_physical_entry inverse (wires 0) (qubits 0)
    (tailPhysicalWires wires) (fun i => qubits i.succ) Reference outcome row column,
    nativeHadamard_reference_matrix_entry wires qubits Reference row column]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical
