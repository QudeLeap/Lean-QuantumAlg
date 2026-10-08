/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.MeasuredSupport
import all QuantumAlg.Core.Execution.Selected.Store
import all QuantumAlg.Core.Execution.Store.Blocks

/-!
# The actual stored X correction has zero output numerator

On every actual stored measurement block, the selected native X sequence
has the complete basis action that keeps the remaining source frame and
sets Y to zero. Combining that literal matrix column with the actual
measurement support annihilates every output row with nonzero Y, including
all external-reference off-diagonal entries and zero-probability blocks
[LYL+26, sec_point_add/sec_point_add.tex:67-81].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorResetMatrix

noncomputable section

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement NumeratorObservation

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The native prefix retains every coordinate above Y, including all EEA history. -/
def framePrefix (width : Nat) (basis : (context width).register.Index) :
    Fin (2 ^ (encoding width).width) :=
  ((prodEquiv (m := (encoding width).width) (n := width)).symm (frameBasis width basis)).1

/-- The actual selected reset has a literal delta column on its own measured outcome. -/
theorem member_column (width : Nat) (value : CShape.Value (.fixedVector width (.finite 2)))
    (source row : (context width).register.Index)
    (same : word width source = NumeratorReset.outcome value) :
    (NumeratorRuntime.program width (NumeratorReset.member width value)).matrix row source =
      (NormalizedVector.ket (R := Qubits (OutputCopy.encoding width).width)
        (prodEquiv (framePrefix width source, (0 : Fin (2 ^ width))))) (frameBasis width row) := by
  have packed : prodEquiv (framePrefix width source, word width source) = frameBasis width source :=
    (prodEquiv (m := (encoding width).width) (n := width)).apply_symm_apply _
  have actual : prodEquiv (framePrefix width source, NumeratorReset.outcome value) =
      frameBasis width source :=
    (congrArg (fun label : Fin (2 ^ width) =>
      prodEquiv (framePrefix width source, label)) same).symm.trans packed
  have column := congrArg
    (fun vector : NormalizedVector (Qubits (OutputCopy.encoding width).width) =>
      vector (frameBasis width row))
    (NumeratorReset.member_ket width value (framePrefix width source))
  have matrixColumn := (HilbertOperator.applyVec_ket
    ((NumeratorReset.member width value).binaryMatrix :
      HilbertOperator (Qubits (OutputCopy.encoding width).width))
    (prodEquiv (framePrefix width source, NumeratorReset.outcome value))
      (frameBasis width row)).symm.trans column
  rw [NumeratorRuntime.program_binary_matrix, ← actual]
  exact matrixColumn

/-- No actual reset column on its measured support has an output with nonzero Y. -/
theorem member_zero (width : Nat) (value : CShape.Value (.fixedVector width (.finite 2)))
    (source row : (context width).register.Index)
    (same : word width source = NumeratorReset.outcome value) (nonzero : word width row ≠ 0) :
    (NumeratorRuntime.program width (NumeratorReset.member width value)).matrix row source = 0 := by
  classical
  rw [member_column width value source row same]
  refine (NormalizedVector.ket_apply (R := Qubits (OutputCopy.encoding width).width)
    (prodEquiv (framePrefix width source, (0 : Fin (2 ^ width)))) (frameBasis width row)).trans ?_
  apply if_neg
  intro equal
  have low := congrArg
    (fun label : Fin (2 ^ (OutputCopy.encoding width).width) =>
      ((prodEquiv (m := (encoding width).width) (n := width)).symm label).2) equal
  have zero : word width row = 0 := by
    simpa only [word, Equiv.symm_apply_apply] using low
  exact nonzero zero

/-- The selected actual reset on a real stored measurement block keeps every reference entry. -/
def density (width : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context width)) :
    DensityOperator (Register.prod (context width).register Reference) :=
  DensityOperator.applyUnitary
    (UnitaryOperator.prodTensor
      (NumeratorRuntime.program width
        (NumeratorReset.member width (stored.read (input width)))).matrix
      (1 : UnitaryOperator Reference))
    (NumeratorMeasuredSupport.density width state stored)

/-- Every full output row with nonzero Y vanishes, including all reference coordinates. -/
theorem row_zero (width : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context width))
    (left right : (context width).register.Index) (leftRef rightRef : Reference.Index)
    (nonzero : word width left ≠ 0) :
    (density width state stored).matrix (left, leftRef) (right, rightRef) = 0 := by
  classical
  rw [density, DensityOperator.localUnitary_block]
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_eq_zero
  intro column _
  apply mul_eq_zero_of_left
  apply Finset.sum_eq_zero
  intro source _
  by_cases same : word width source = NumeratorReset.outcome (stored.read (input width))
  · rw [member_zero width (stored.read (input width)) source left same nonzero, zero_mul]
  · rw [NumeratorMeasuredSupport.row_zero width state stored source column leftRef rightRef same,
      mul_zero]

/-- This density is the actual sequential Z-write and stored-result reset block. -/
theorem actual_density (width : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context width)) :
    (ExecutionState.filterClassical
      ((Circuit.seq (NumeratorMeasurement.measure width) (NumeratorReset.reset width)).execute
        Reference state) (fun entry => entry.1 = stored)).quantumMarginal =
      density width state stored := by
  rw [Circuit.seq_store_marginal]
  apply DensityOperator.ext
  exact Circuit.selectedUnitary_store_matrix (input width)
    (fun value => NumeratorRuntime.program width (NumeratorReset.member width value))
    ((NumeratorMeasurement.measure width).execute Reference state) stored

/-- The complete actual H/Z/reset sequence has no output numerator support away from zero. -/
theorem actual_code_row_zero (width : Nat) {Reference : Register} {History : Type}
    [Fintype History] (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (context width))
    (left right : (context width).register.Index) (leftRef rightRef : Reference.Index)
    (nonzero : word width left ≠ 0) :
    (ExecutionState.filterClassical ((NumeratorReset.code width).execute Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal.matrix (left, leftRef) (right, rightRef) =
      0 := by
  change (ExecutionState.filterClassical
    ((Circuit.seq (NumeratorReset.hadamard width)
      (.seq (NumeratorMeasurement.measure width) (NumeratorReset.reset width))).execute
      Reference state) (fun entry => entry.1 = stored)).quantumMarginal.matrix _ _ = 0
  rw [Circuit.seq_store_marginal, actual_density]
  exact row_zero width ((NumeratorReset.hadamard width).execute Reference state) stored
    left right leftRef rightRef nonzero

end

end QuantumAlg.MeasuredUncompute.NumeratorResetMatrix
