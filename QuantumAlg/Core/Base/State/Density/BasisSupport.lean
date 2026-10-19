/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Util.Matrix.PosSemidef

/-!
# Local basis support retains every reference correlation

A zero diagonal entry of a positive density matrix forces its complete
row and column to vanish. A zero diagonal in a local marginal consequently
forces that same support restriction on every joint reference coordinate.
No separability, purity, or nonzero probability assumption is used.

Two local operators whose columns agree on this support therefore induce
the same full joint conjugation. These are matrix consequences of positive
density operators and the existing tensor/unitary rules
[dW19, qcnotes.tex:5381,5394,5405,6827]. They define no execution instruction,
measurement framework, or resource cost.
-/

namespace QuantumAlg.DensityOperator

noncomputable section

open scoped ComplexOrder

variable {R Reference : Register}

/-- Zero diagonal weight annihilates every entry of the same complete column. -/
lemma column_zero_of_diagonal_zero (state : DensityOperator R) (basis : R.Index)
    (zero : state.matrix basis basis = 0) (row : R.Index) : state.matrix row basis = 0 := by
  classical
  have quadratic : dotProduct (star (Pi.single basis (1 : ℂ)))
      (Matrix.mulVec state.matrix (Pi.single basis (1 : ℂ))) = 0 := by
    simpa only [Pi.star_single, star_one, Matrix.mulVec_single_one,
      single_one_dotProduct, Matrix.col_apply] using zero
  have kernel := state.positive.mulVec_eq_zero_of_quadratic_eq_zero
    (Pi.single basis (1 : ℂ)) quadratic
  have coordinate := congrFun kernel row
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] using coordinate

/-- Hermitian symmetry also annihilates every entry of the complete corresponding row. -/
lemma row_zero_of_diagonal_zero (state : DensityOperator R) (basis : R.Index)
    (zero : state.matrix basis basis = 0) (column : R.Index) : state.matrix basis column = 0 := by
  rw [← state.positive.isHermitian.apply basis column,
    column_zero_of_diagonal_zero state basis zero column, star_zero]

/-- A vanishing local diagonal forces every associated joint-reference diagonal to vanish. -/
lemma joint_diagonal_zero_of_marginal_diagonal_zero
    (state : DensityOperator (Register.prod R Reference)) (basis : R.Index)
    (zero : state.marginalLeft.matrix basis basis = 0) (reference : Reference.Index) :
    state.matrix (basis, reference) (basis, reference) = 0 := by
  classical
  have bound : state.matrix (basis, reference) (basis, reference) ≤
      ∑ current : Reference.Index, state.matrix (basis, current) (basis, current) :=
    Finset.single_le_sum (fun current _ =>
      state.positive.diag_nonneg (i := (basis, current))) (Finset.mem_univ reference)
  have total : (∑ current : Reference.Index,
      state.matrix (basis, current) (basis, current)) = 0 :=
    (marginalLeft_matrix state basis basis).symm.trans zero
  exact le_antisymm (bound.trans_eq total) state.positive.diag_nonneg

/-- Local support controls the full joint row, including off-diagonal reference data. -/
lemma joint_row_zero_of_marginal_diagonal_zero
    (state : DensityOperator (Register.prod R Reference)) (basis : R.Index)
    (zero : state.marginalLeft.matrix basis basis = 0)
    (reference : Reference.Index) (column : (Register.prod R Reference).Index) :
    state.matrix (basis, reference) column = 0 :=
  row_zero_of_diagonal_zero state (basis, reference)
    (joint_diagonal_zero_of_marginal_diagonal_zero state basis zero reference) column

/-- The corresponding complete joint column vanishes for every reference coordinate as well. -/
lemma joint_column_zero_of_marginal_diagonal_zero
    (state : DensityOperator (Register.prod R Reference)) (basis : R.Index)
    (zero : state.marginalLeft.matrix basis basis = 0)
    (reference : Reference.Index) (row : (Register.prod R Reference).Index) :
    state.matrix row (basis, reference) = 0 :=
  column_zero_of_diagonal_zero state (basis, reference)
    (joint_diagonal_zero_of_marginal_diagonal_zero state basis zero reference) row

/-- Columns agreeing on actual density support give the same complete matrix conjugation. -/
lemma conjugation_eq_on_basis_support (state : DensityOperator R)
    (admissible : R.Index → Prop) (left right : HilbertOperator R)
    (support : ∀ basis, ¬admissible basis → state.matrix basis basis = 0)
    (columns : ∀ basis, admissible basis → ∀ row, left row basis = right row basis) :
    left * state.matrix * left.conjTranspose = right * state.matrix * right.conjTranspose := by
  classical
  have product : left * state.matrix = right * state.matrix := by
    ext row column
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro basis _
    by_cases allowed : admissible basis
    · exact congrArg (fun coefficient => coefficient * state.matrix basis column)
        (columns basis allowed row)
    · rw [row_zero_of_diagonal_zero state basis (support basis allowed) column,
        mul_zero, mul_zero]
  have adjoint : state.matrix * left.conjTranspose = state.matrix * right.conjTranspose := by
    have same := congrArg Matrix.conjTranspose product
    simpa only [Matrix.conjTranspose_mul, state.positive.isHermitian.eq] using same
  calc
    _ = right * state.matrix * left.conjTranspose :=
      congrArg (fun value => value * left.conjTranspose) product
    _ = right * (state.matrix * left.conjTranspose) := Matrix.mul_assoc _ _ _
    _ = right * (state.matrix * right.conjTranspose) :=
      congrArg (fun value => right * value) adjoint
    _ = _ := (Matrix.mul_assoc _ _ _).symm

/-- Local column equality on locally observable support gives equal full joint unitary evolution. -/
lemma applyLocalUnitary_eq_on_basis_support
    (state : DensityOperator (Register.prod R Reference)) (admissible : R.Index → Prop)
    (left right : UnitaryOperator R)
    (support : ∀ basis, ¬admissible basis → state.marginalLeft.matrix basis basis = 0)
    (columns : ∀ basis, admissible basis → ∀ row, left row basis = right row basis) :
    applyUnitary (UnitaryOperator.prodTensor left (1 : UnitaryOperator Reference)) state =
      applyUnitary (UnitaryOperator.prodTensor right (1 : UnitaryOperator Reference)) state := by
  apply DensityOperator.ext
  apply conjugation_eq_on_basis_support state (fun basis => admissible basis.1)
  · intro basis absent
    exact joint_diagonal_zero_of_marginal_diagonal_zero state basis.1
      (support basis.1 absent) basis.2
  · intro basis allowed row
    change left row.1 basis.1 * (1 : HilbertOperator Reference) row.2 basis.2 =
      right row.1 basis.1 * (1 : HilbertOperator Reference) row.2 basis.2
    exact congrArg (fun coefficient => coefficient * (1 : HilbertOperator Reference) row.2 basis.2)
      (columns basis.1 allowed row.1)

end

end QuantumAlg.DensityOperator
