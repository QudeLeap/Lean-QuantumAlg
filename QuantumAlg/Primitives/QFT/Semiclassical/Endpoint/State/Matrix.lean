/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.State.Coordinates
import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Specification
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.SourceRows
import all QuantumAlg.Core.Base.Gate.Unitary.Permutation
import all QuantumAlg.Core.Measure.Kraus
import all QuantumAlg.Core.Measure.Instrument
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Derived Fourier rows and the independent dephasing target

The two signs use the same physical no-SWAP wire order: row reversal followed
by the forward Fourier operator or its inverse. A retained row Kraus matrix
is exactly the computational-basis projector after that operator tensored
with the reference identity. Summing these real branches is the independent
bank-reference dephasing specified at the endpoint.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint

noncomputable section

open MeasurementInstrument
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- The independent no-SWAP target reverses the output row, for either Fourier sign. -/
lemma idealOperator_entry (inverse : Bool) (n : Nat) (row column : Fin (2 ^ n)) :
    idealOperator inverse n row column =
      (if inverse then (QFTOperator n)⁻¹ else QFTOperator n)
        (qftReverseBits n row) column := by
  let signed : UnitaryOperator (Qubits n) :=
    if inverse then (QFTOperator n)⁻¹ else QFTOperator n
  change
    ((UnitaryOperator.ofPerm (R := Qubits n) (qftReverseBitsPerm n) :
      HilbertOperator (Qubits n)) * (signed : HilbertOperator (Qubits n)))
      row column = signed (qftReverseBits n row) column
  simp only [Matrix.mul_apply, UnitaryOperator.ofPerm_entry, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

/-- The complete derived native source row equals the independently specified Fourier row. -/
lemma signedSourceMatrix_ideal_entry (inverse : Bool) (n : Nat) (row column : Bits n) :
    signedSourceMatrix inverse n row column =
      idealOperator inverse n (binaryEquiv n row) (binaryEquiv n column) := by
  cases inverse with
  | false =>
      rw [idealOperator_entry]
      exact qftSemiclassical_coherent_entry n row column
  | true =>
      rw [signedSourceMatrix_inverse .empty
        (environment := OracleModel.emptyInterpretation), idealOperator_entry]
      change star (sourceMatrix .empty n OracleModel.emptyInterpretation row column) =
        star (QFTOperator n (binaryEquiv n column) (qftReverseBits n (binaryEquiv n row)))
      rw [← qftSemiclassical_coherent_eq_sourceMatrix .empty OracleModel.emptyInterpretation,
        qftSemiclassical_coherent_entry]
      congr 1
      simp only [QFTOperator_entry, Nat.mul_comm]

/-- Exact full-bank/reference coordinates of the endpoint, with no physical operation. -/
def outputJointBasis (n : Nat) (Reference : Register) :
    ((outputContext n).register.prod Reference).Index ≃ ((Qubits n).prod Reference).Index :=
  (outputBasisEquiv n).prodCongr (Equiv.refl Reference.Index)

/-- Native branch entries are the literal ideal row Kraus matrix on the actual physical bank. -/
lemma sourceOutcomeKraus_endpoint_entry (inverse : Bool) (n : Nat)
    (Reference : Register) (outcome : Bits n)
    (row column : ((outputContext n).register.prod Reference).Index) :
    sourceOutcomeKraus inverse Reference n (wires n) (qftSemiclassical_wires_qubits n)
      outcome row column =
      bankKraus (binaryEquiv n outcome)
        (rowKraus (idealOperator inverse n : HilbertOperator (Qubits n)) (binaryEquiv n outcome))
        (outputJointBasis n Reference row) (outputJointBasis n Reference column) := by
  have selected :
      (bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) row.1).1 = outcome ↔
        outputBasisEquiv n row.1 = binaryEquiv n outcome := by
    rw [← bankCoordinates_output_label]
    exact (binaryEquiv n).injective.eq_iff.symm
  have rest :
      ((bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) row.1).2, row.2) =
        ((bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) column.1).2, column.2) ↔
          row.2 = column.2 := by
    constructor
    · intro same
      exact (Prod.mk.inj same).2
    · intro same
      exact Prod.ext (bankCoordinates_output_complement n row.1 column.1) same
  let amplitude : Complex :=
    (signedSourceMatrix inverse n : Matrix (Bits n) (Bits n) Complex) outcome
      (bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) column.1).1
  have amplitudeEq : amplitude =
      idealOperator inverse n (binaryEquiv n outcome) (outputBasisEquiv n column.1) := by
    calc
      amplitude = idealOperator inverse n (binaryEquiv n outcome)
          (binaryEquiv n
            (bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) column.1).1) :=
        signedSourceMatrix_ideal_entry inverse n outcome
          (bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) column.1).1
      _ = idealOperator inverse n (binaryEquiv n outcome) (outputBasisEquiv n column.1) :=
        congrArg
          (fun basis : Fin (2 ^ n) => idealOperator inverse n (binaryEquiv n outcome) basis)
          (bankCoordinates_output_label n column.1)
  change
    (if (bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) row.1).1 = outcome ∧
        ((bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) row.1).2, row.2) =
          ((bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) column.1).2, column.2) then
      amplitude else 0) =
      bankKraus (binaryEquiv n outcome)
        (rowKraus (idealOperator inverse n : HilbertOperator (Qubits n)) (binaryEquiv n outcome))
        (outputBasisEquiv n row.1, row.2) (outputBasisEquiv n column.1, column.2)
  rw [bankKraus_coherent_entry]
  by_cases bank : outputBasisEquiv n row.1 = binaryEquiv n outcome
  · have sourceBank := selected.mpr bank
    by_cases reference : row.2 = column.2
    · have sourceRest := rest.mpr reference
      rw [if_pos ⟨sourceBank, sourceRest⟩, if_pos bank, if_pos reference, mul_one]
      exact amplitudeEq
    · have absent : ¬
          ((bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) row.1).1 = outcome ∧
            ((bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) row.1).2, row.2) =
              ((bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) column.1).2,
                column.2)) := fun same => reference (rest.mp same.2)
      rw [if_neg absent, if_pos bank, if_neg reference, mul_zero]
  · have absent : ¬
        ((bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) row.1).1 = outcome ∧
          ((bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) row.1).2, row.2) =
            ((bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) column.1).2,
              column.2)) := fun same => bank (selected.mp same.1)
    rw [if_neg absent, if_neg bank, zero_mul]

private lemma bankKraus_eq_projector {R Reference : Register}
    (operator : UnitaryOperator R) (outcome : R.Index) :
    bankKraus (R := Reference.Index) outcome
        (rowKraus (operator : HilbertOperator R) outcome) =
      ZMeasurement.projector (R := R.prod Reference) (fun basis => basis.1) outcome *
        (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference) :
          HilbertOperator (R.prod Reference)) := by
  ext ⟨row, leftRef⟩ ⟨column, rightRef⟩
  rw [bankKraus_coherent_entry, ZMeasurement.projector, Matrix.diagonal_mul,
    UnitaryOperator.prodTensor_apply]
  change (if row = outcome then operator outcome column else 0) *
      (if leftRef = rightRef then 1 else 0) =
    (if row = outcome then 1 else 0) *
      (operator row column * (if leftRef = rightRef then 1 else 0))
  by_cases same : row = outcome
  · subst row
    simp only [if_true, one_mul]
  · simp only [same, if_false, zero_mul]

/-- An actual retained Fourier row is ideal unitary evolution followed by its basis projector. -/
lemma bankBranch_eq_measured_unitary {R Reference : Register}
    (operator : UnitaryOperator R) (state : DensityOperator (R.prod Reference))
    (outcome : R.Index) :
    bankBranch outcome (rowKraus (operator : HilbertOperator R) outcome) state.matrix =
      (ZMeasurement.branch (R := R.prod Reference) (fun basis => basis.1) outcome
        (DensityOperator.applyUnitary
          (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference)) state)).matrix := by
  let projection : HilbertOperator (R.prod Reference) :=
    ZMeasurement.projector (R := R.prod Reference) (fun basis => basis.1) outcome
  let transform : HilbertOperator (R.prod Reference) :=
    (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference) :
      HilbertOperator (R.prod Reference))
  unfold bankBranch
  rw [bankKraus_eq_projector]
  change (projection * transform) * state.matrix *
      (projection * transform).conjTranspose =
    projection * (transform * state.matrix * transform.conjTranspose) * projection.conjTranspose
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- Summing every row branch is precisely the independent full-bank dephasing instrument. -/
lemma sum_bankBranch_eq_dephasing {R Reference : Register}
    (operator : UnitaryOperator R) (state : DensityOperator (R.prod Reference)) :
    (∑ outcome : R.Index,
      bankBranch outcome (rowKraus (operator : HilbertOperator R) outcome) state.matrix) =
      ((ExecutionState.ofValue ()
        (DensityOperator.applyUnitary
          (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference)) state)).measureZ
            (fun basis => basis.1)).quantumMarginal.matrix := by
  simp_rw [bankBranch_eq_measured_unitary]
  change (∑ outcome : R.Index, _) = ∑ record : Unit × R.Index, _
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, ExecutionState.measureZ_block,
    ExecutionState.ofValue_block, if_true]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint
