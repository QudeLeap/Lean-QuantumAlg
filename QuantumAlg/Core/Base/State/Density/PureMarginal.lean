/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Util.Matrix.PosSemidef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Joint matrix support forced by a pure marginal

A pure left marginal forces the full positive joint matrix onto that same
one-dimensional left subspace. The right subsystem is unrestricted. This
matrix fact preserves off-diagonal correlations and does not assume a product
input or introduce an additional quantum-state carrier.
-/

open scoped ComplexOrder
open Kronecker

namespace QuantumAlg.DensityOperator

noncomputable section

variable {R S : Register}

/-- Lift a local matrix without changing the actual product-register carrier. -/
private def leftTensor (operator : HilbertOperator R) : HilbertOperator (Register.prod R S) :=
  operator ⊗ₖ (1 : HilbertOperator S)

private lemma leftTensor_conjTranspose (operator : HilbertOperator R) :
    (leftTensor (S := S) operator).conjTranspose =
      leftTensor (S := S) operator.conjTranspose := by
  change (operator ⊗ₖ (1 : HilbertOperator S)).conjTranspose =
    operator.conjTranspose ⊗ₖ (1 : HilbertOperator S)
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

/-- The pure-state matrix is an actual rank-one projector on any finite register. -/
lemma ofPure_matrix_idempotent (state : NormalizedVector R) :
    (ofPure state).matrix * (ofPure state).matrix = (ofPure state).matrix := by
  have normalized : (∑ index : R.Index, state index * star (state index)) = 1 :=
    trace_pureMatrix state
  ext row column
  rw [Matrix.mul_apply]
  simp only [ofPure_matrix]
  calc
    (∑ index, (state row * star (state index)) * (state index * star (state column))) =
        (state row * star (state column)) * ∑ index, state index * star (state index) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ = state row * star (state column) := by rw [normalized, mul_one]

private lemma mul_leftTensor_entry (state : DensityOperator (Register.prod R S))
    (operator : HilbertOperator R) (row column : R.Index) (rightRow rightColumn : S.Index) :
    (state.matrix * leftTensor (S := S) operator)
        (row, rightRow) (column, rightColumn) =
      ∑ index : R.Index, state.matrix (row, rightRow) (index, rightColumn) *
        operator index column := by
  rw [Matrix.mul_apply]
  change (∑ pair : R.Index × S.Index, state.matrix (row, rightRow) pair *
    (operator pair.1 column * (1 : HilbertOperator S) pair.2 rightColumn)) = _
  rw [Fintype.sum_prod_type]
  simp [Matrix.one_apply, mul_ite]

private lemma leftTensor_mul_entry (state : DensityOperator (Register.prod R S))
    (operator : HilbertOperator R) (row column : R.Index) (rightRow rightColumn : S.Index) :
    (leftTensor (S := S) operator * state.matrix)
        (row, rightRow) (column, rightColumn) =
      ∑ index : R.Index, operator row index *
        state.matrix (index, rightRow) (column, rightColumn) := by
  rw [Matrix.mul_apply]
  change (∑ pair : R.Index × S.Index,
    (operator row pair.1 * (1 : HilbertOperator S) rightRow pair.2) *
      state.matrix pair (column, rightColumn)) = _
  rw [Fintype.sum_prod_type]
  simp [Matrix.one_apply, mul_ite, ite_mul]

private lemma trace_mul_leftTensor (state : DensityOperator (Register.prod R S))
    (operator : HilbertOperator R) :
    (state.matrix * leftTensor (S := S) operator).trace =
      (state.marginalLeft.matrix * operator).trace := by
  change (∑ pair : R.Index × S.Index,
    (state.matrix * leftTensor (S := S) operator) pair pair) =
      ∑ row : R.Index, ∑ index : R.Index,
        state.marginalLeft.matrix row index * operator index row
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro row _
  calc
    _ = ∑ right : S.Index, ∑ index : R.Index,
        state.matrix (row, right) (index, right) * operator index row :=
      Finset.sum_congr rfl fun right _ => mul_leftTensor_entry state operator row row right right
    _ = ∑ index : R.Index, ∑ right : S.Index,
        state.matrix (row, right) (index, right) * operator index row := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index _
      rw [← Finset.sum_mul]
      exact congrArg (fun value : ℂ => value * operator index row)
        (marginalLeft_matrix (R := R) (S := S) state row index).symm

/-- A pure left marginal forces exact right support of the entire joint matrix.
The equation retains every right-system matrix coordinate. -/
lemma mul_pureMarginal_projector (state : DensityOperator (Register.prod R S))
    (pure : NormalizedVector R) (promised : state.marginalLeft = ofPure pure) :
    state.matrix * leftTensor (S := S) (ofPure pure).matrix = state.matrix := by
  let projector := (ofPure pure).matrix
  let complement : HilbertOperator R := 1 - projector
  let lifted := leftTensor (S := S) complement
  have projectorSelfAdjoint : projector.conjTranspose = projector :=
    (ofPure pure).positive.isHermitian.eq
  have projectorSquared : projector * projector = projector := ofPure_matrix_idempotent pure
  have complementSelfAdjoint : complement.conjTranspose = complement := by
    dsimp only [complement]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, projectorSelfAdjoint]
  have complementSquared : complement * complement = complement := by
    change (1 - projector) * (1 - projector) = 1 - projector
    simp only [sub_mul, mul_sub, one_mul, mul_one, projectorSquared, sub_self, sub_zero]
  have liftedSelfAdjoint : lifted.conjTranspose = lifted := by
    dsimp only [lifted, leftTensor]
    rw [Matrix.conjTranspose_kronecker, complementSelfAdjoint, Matrix.conjTranspose_one]
  have liftedSquared : lifted * lifted = lifted := by
    dsimp only [lifted, leftTensor]
    rw [← Matrix.mul_kronecker_mul, complementSquared, mul_one]
  have traceZero : (lifted.conjTranspose * state.matrix * lifted).trace = 0 := by
    calc
      _ = (lifted * lifted.conjTranspose * state.matrix).trace :=
        Matrix.trace_mul_cycle _ _ _
      _ = (state.matrix * lifted).trace := by
        rw [liftedSelfAdjoint, liftedSquared, Matrix.trace_mul_comm]
      _ = (state.marginalLeft.matrix * complement).trace :=
        trace_mul_leftTensor state complement
      _ = 0 := by
        rw [promised]
        change (projector * (1 - projector)).trace = 0
        rw [mul_sub, mul_one, projectorSquared, sub_self, Matrix.trace_zero]
  have compressionZero : lifted.conjTranspose * state.matrix * lifted = 0 :=
    (state.positive.conjTranspose_mul_mul_same lifted).trace_eq_zero_iff.mp traceZero
  have annihilates : state.matrix * lifted = 0 :=
    state.positive.mul_eq_zero_of_compression_eq_zero lifted compressionZero
  have liftedComplement : lifted =
      1 - leftTensor (S := S) projector := by
    calc
      _ = leftTensor (S := S) (1 : HilbertOperator R) -
          leftTensor (S := S) projector := by
        ext row column
        exact sub_mul _ _ _
      _ = _ := by rw [leftTensor, Matrix.one_kronecker_one]
  rw [liftedComplement, mul_sub, mul_one] at annihilates
  exact (sub_eq_zero.mp annihilates).symm

/-- Hermitian symmetry yields the corresponding left support, with no lost coherences. -/
lemma pureMarginal_projector_mul (state : DensityOperator (Register.prod R S))
    (pure : NormalizedVector R) (promised : state.marginalLeft = ofPure pure) :
    leftTensor (S := S) (ofPure pure).matrix * state.matrix = state.matrix := by
  have adjoint := congrArg Matrix.conjTranspose (mul_pureMarginal_projector state pure promised)
  simpa only [Matrix.conjTranspose_mul, leftTensor_conjTranspose,
    (ofPure pure).positive.isHermitian.eq,
    state.positive.isHermitian.eq] using adjoint

private lemma pureMarginal_row (state : DensityOperator (Register.prod R S))
    (pure : NormalizedVector R) (promised : state.marginalLeft = ofPure pure)
    (row column : R.Index) (rightRow rightColumn : S.Index) :
    state.matrix (row, rightRow) (column, rightColumn) =
      ∑ index : R.Index, (pure row * star (pure index)) *
        state.matrix (index, rightRow) (column, rightColumn) := by
  have entry := congrArg (fun matrix : HilbertOperator (Register.prod R S) =>
      matrix (row, rightRow) (column, rightColumn))
    (pureMarginal_projector_mul state pure promised).symm
  exact entry.trans (leftTensor_mul_entry state (ofPure pure).matrix
    row column rightRow rightColumn)

private lemma pureMarginal_column (state : DensityOperator (Register.prod R S))
    (pure : NormalizedVector R) (promised : state.marginalLeft = ofPure pure)
    (row column : R.Index) (rightRow rightColumn : S.Index) :
    state.matrix (row, rightRow) (column, rightColumn) =
      ∑ index : R.Index, state.matrix (row, rightRow) (index, rightColumn) *
        (pure index * star (pure column)) := by
  have entry := congrArg (fun matrix : HilbertOperator (Register.prod R S) =>
      matrix (row, rightRow) (column, rightColumn))
    (mul_pureMarginal_projector state pure promised).symm
  exact entry.trans (mul_leftTensor_entry state (ofPure pure).matrix
    row column rightRow rightColumn)

private def jointCoefficient (state : DensityOperator (Register.prod R S))
    (pure : NormalizedVector R) (rightRow rightColumn : S.Index) : ℂ :=
  ∑ row : R.Index, ∑ column : R.Index,
    star (pure row) * state.matrix (row, rightRow) (column, rightColumn) * pure column

private lemma pureMarginal_coefficient_entry (state : DensityOperator (Register.prod R S))
    (pure : NormalizedVector R) (promised : state.marginalLeft = ofPure pure)
    (row column : R.Index) (rightRow rightColumn : S.Index) :
    state.matrix (row, rightRow) (column, rightColumn) =
      (pure row * star (pure column)) * jointCoefficient state pure rightRow rightColumn := by
  calc
    _ = ∑ index : R.Index, (pure row * star (pure index)) *
        state.matrix (index, rightRow) (column, rightColumn) :=
      pureMarginal_row state pure promised row column rightRow rightColumn
    _ = ∑ index : R.Index, (pure row * star (pure index)) *
        ∑ other : R.Index, state.matrix (index, rightRow) (other, rightColumn) *
          (pure other * star (pure column)) := by
      apply Finset.sum_congr rfl
      intro index _
      rw [pureMarginal_column state pure promised index column rightRow rightColumn]
    _ = _ := by
      unfold jointCoefficient
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      apply Finset.sum_congr rfl
      intro other _
      ring

/-- A promised pure left marginal forces the full joint matrix to factor with
its actual right marginal. Every off-diagonal right entry is retained; no
product-state or external-reference assumption is supplied by the caller. -/
public lemma pureMarginal_entry (state : DensityOperator (Register.prod R S))
    (pure : NormalizedVector R) (promised : state.marginalLeft = ofPure pure)
    (row column : R.Index) (rightRow rightColumn : S.Index) :
    state.matrix (row, rightRow) (column, rightColumn) =
      (pure row * star (pure column)) *
        ∑ index : R.Index, state.matrix (index, rightRow) (index, rightColumn) := by
  have marginal : (∑ index : R.Index, state.matrix (index, rightRow) (index, rightColumn)) =
      jointCoefficient state pure rightRow rightColumn := by
    calc
      _ = ∑ index : R.Index, (pure index * star (pure index)) *
          jointCoefficient state pure rightRow rightColumn :=
        Finset.sum_congr rfl fun index _ =>
          pureMarginal_coefficient_entry state pure promised index index rightRow rightColumn
      _ = (∑ index : R.Index, pure index * star (pure index)) *
          jointCoefficient state pure rightRow rightColumn := (Finset.sum_mul ..).symm
      _ = jointCoefficient state pure rightRow rightColumn := by
        have normalized : (∑ index : R.Index, pure index * star (pure index)) = 1 :=
          trace_pureMatrix pure
        rw [normalized, one_mul]
  rw [marginal]
  exact pureMarginal_coefficient_entry state pure promised row column rightRow rightColumn

end

end QuantumAlg.DensityOperator
