/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.State.Coordinates
import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.State.Matrix
import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Construction
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Observation
import all QuantumAlg.Core.Execution.Pure.Selection

/-!
# The actual stored vector selects its retained physical bank

The fine-model body executes its literal H, Z measurement and stored feedback
instructions. Its observed result is the real vector of retained cells. The
conditional full density is the derived source-row branch of the original
mixed input. Zero rows then establish the corresponding pure bank promise at
the branch's original probability mass, without a product-state assumption.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint

noncomputable section

open Execution
open MeasurementInstrument
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- The independent ideal instrument acting on the body's complete actual input density. -/
def bodyIdealState (inverse : Bool) (n : Nat) (Reference : Register)
    (state : DensityOperator ((outputContext n).register.prod Reference)) :
    DensityOperator ((outputContext n).register.prod Reference) :=
  (((ExecutionState.ofValue ()
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (idealOperator inverse n) (1 : UnitaryOperator Reference))
      (state.reindex (outputJointBasis n Reference)))).measureZ
        (fun basis => basis.1)).quantumMarginal).reindex
          (outputJointBasis n Reference).symm

private lemma conjugation_coordinates {I J : Type} [Fintype I] [Fintype J]
    (basis : I ≃ J) (operator : Matrix J J Complex) (density : Matrix I I Complex) :
    operator.submatrix basis basis * density *
        (operator.submatrix basis basis).conjTranspose =
      (operator * density.submatrix basis.symm basis.symm * operator.conjTranspose).submatrix
        basis basis := by
  have original : (density.submatrix basis.symm basis.symm).submatrix basis basis = density := by
    ext row column
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  calc
    _ = operator.submatrix basis basis *
        (density.submatrix basis.symm basis.symm).submatrix basis basis *
          (operator.submatrix basis basis).conjTranspose := by rw [original]
    _ = _ := by
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
        Matrix.submatrix_mul_equiv]

/-- Native conjugation equals the ideal measured branch in the same actual full coordinates. -/
lemma sourceOutcomeKraus_endpoint_conjugation (inverse : Bool) (n : Nat)
    (Reference : Register) (outcome : Bits n)
    (state : DensityOperator ((outputContext n).register.prod Reference)) :
    sourceOutcomeKraus inverse Reference n (wires n) (qftSemiclassical_wires_qubits n)
        outcome * state.matrix *
      (sourceOutcomeKraus inverse Reference n (wires n)
        (qftSemiclassical_wires_qubits n) outcome).conjTranspose =
      (bankBranch (binaryEquiv n outcome)
        (rowKraus (idealOperator inverse n : HilbertOperator (Qubits n))
          (binaryEquiv n outcome))
        (state.reindex (outputJointBasis n Reference)).matrix).submatrix
          (outputJointBasis n Reference) (outputJointBasis n Reference) := by
  have native : sourceOutcomeKraus inverse Reference n (wires n)
      (qftSemiclassical_wires_qubits n) outcome =
      (bankKraus (binaryEquiv n outcome)
        (rowKraus (idealOperator inverse n : HilbertOperator (Qubits n))
          (binaryEquiv n outcome))).submatrix
            (outputJointBasis n Reference) (outputJointBasis n Reference) := by
    ext row column
    exact sourceOutcomeKraus_endpoint_entry inverse n Reference outcome row column
  rw [native]
  exact conjugation_coordinates (outputJointBasis n Reference) _ state.matrix

/-- The literal fine body realizes the independent full bank-reference dephasing target. -/
lemma body_quantumMarginal {environment : (ExecutionModel.quantum SemiclassicalFourierGate.model
    .empty).Environment} (inverse : Bool) (n : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (outputContext n) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (((body inverse n).execute environment) Reference state).quantumMarginal =
      bodyIdealState inverse n Reference state.quantumMarginal := by
  apply DensityOperator.ext
  change (((Refined.code inverse n (wires n) (qftSemiclassical_wires_qubits n)
    (resultCell n)).execute environment) Reference state).quantumMarginal.matrix = _
  rw [refinedCode_source_quantumMarginal_matrix]
  simp_rw [sourceOutcomeKraus_endpoint_conjugation]
  have branches := sum_bankBranch_eq_dephasing (idealOperator inverse n)
    (state.quantumMarginal.reindex (outputJointBasis n Reference))
  have physical := congrArg (fun matrix : HilbertOperator ((Qubits n).prod Reference) =>
    matrix.submatrix (outputJointBasis n Reference) (outputJointBasis n Reference)) branches
  rw [← (binaryEquiv n).sum_comp] at physical
  refine Eq.trans ?_ physical
  ext row column
  simp only [Matrix.sum_apply, Matrix.submatrix_apply]

/-- The observed actual vector fixes the native branch, with the whole reference retained. -/
lemma body_result_matrix {environment : (ExecutionModel.quantum SemiclassicalFourierGate.model
    .empty).Environment} (inverse : Bool) (n : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (outputContext n) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (outcome : Bits n) :
    ((((body inverse n).execute environment) Reference state).mapClassical
      (fun entry => (resultRead n).eval entry.1) |>.block (resultValue n outcome)).matrix =
      sourceOutcomeKraus inverse Reference n (wires n) (qftSemiclassical_wires_qubits n)
        outcome * state.quantumMarginal.matrix *
          (sourceOutcomeKraus inverse Reference n (wires n)
            (qftSemiclassical_wires_qubits n) outcome).conjTranspose := by
  change ((((Refined.code inverse n (wires n) (qftSemiclassical_wires_qubits n)
    (resultCell n)).execute environment) Reference state).mapClassical
      (fun entry => (resultRead n).eval entry.1) |>.block (resultValue n outcome)).matrix = _
  rw [refinedCode_source_read_matrix]
  simp only [resultRead_outcomeStore, (resultValue_injective n).eq_iff,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, sum_store_matrices]

/-- Every source branch has zero rows outside its actual retained physical basis value. -/
lemma sourceOutcomeKraus_endpoint_zero_row (inverse : Bool) (n : Nat)
    (Reference : Register) (outcome : Bits n) (row : (outputContext n).register.Index)
    (different : row ≠ (outputBasisEquiv n).symm (binaryEquiv n outcome))
    (reference : Reference.Index)
    (column : ((outputContext n).register.prod Reference).Index) :
    sourceOutcomeKraus inverse Reference n (wires n) (qftSemiclassical_wires_qubits n)
      outcome (row, reference) column = 0 := by
  have outside := bankCoordinates_output_ne n outcome row different
  simp only [sourceOutcomeKraus, referenceBankCoordinates_apply, outside, false_and, if_false]

/-- The actual conditional bank is pure even for entangled inputs and zero-probability outputs. -/
lemma body_result_pure {environment : (ExecutionModel.quantum SemiclassicalFourierGate.model
    .empty).Environment} (inverse : Bool) (n : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (outputContext n) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (value : CShape.Value (.fixedVector n (.finite 2))) :
    (StatePromise.pure (NormalizedVector.ket
      ((outputContext n).quantumLayout.restrictSelectedBasis Finset.univ
        ((outputBasisEquiv n).symm (physicalLabel n value))))).Holds
      (DensityOperator.observeSelection (outputContext n).quantumLayout Finset.univ Reference
        (((((body inverse n).execute environment) Reference state).mapClassical
          (fun entry => (resultRead n).eval entry.1)).block value)) := by
  obtain ⟨outcome, rfl⟩ := resultValue_surjective n value
  rw [physicalLabel_resultValue]
  apply StatePromise.pureKet_fullSelection_of_localMarginal
  apply StatePromise.statePromise_pureKet_of_row_support
  intro row different column
  rw [DensityOperator.marginalLeft_matrix]
  apply Finset.sum_eq_zero
  intro reference _
  rw [body_result_matrix]
  simp only [Matrix.mul_apply,
    sourceOutcomeKraus_endpoint_zero_row inverse n Reference outcome row different,
    zero_mul, Finset.sum_const_zero]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint
