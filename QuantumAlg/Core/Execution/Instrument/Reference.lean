/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ExecutionState

public import QuantumAlg.Core.Base.Tensor.Certified

import all QuantumAlg.Core.Base.Tensor.Reference
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Untouched-reference unitaries commute with full retained Kraus blocks

The complete block equation of an actual interpreter is the premise. Every
original classical record and outcome is retained, including Store-overwrite
collisions. Local operators are arbitrary matrices, so this law imposes no
arithmetic domain or good-label condition. Its use for a concrete allocating
Driver still requires that Driver's actual full-record Kraus equation.
-/

@[expose] public section

namespace QuantumAlg.Execution.Instrument

noncomputable section

open scoped BigOperators Kronecker

attribute [local instance] Classical.decEq

variable {Local Reference : Register}

/-- The local matrix on the same complete product carrier, with unchanged reference entries. -/
def referenceLift (Reference : Register) (operator : HilbertOperator Local) :
    HilbertOperator (Local.prod Reference) :=
  fun row column => operator row.1 column.1 *
    (if row.2 = column.2 then 1 else 0)

/-- An arbitrary reference matrix acting beside the untouched local register. -/
def referenceAction (Local : Register) (operator : HilbertOperator Reference) :
    HilbertOperator (Local.prod Reference) :=
  fun row column => (if row.1 = column.1 then 1 else 0) * operator row.2 column.2

/-- Pure matrix locality, without a unitary or canonical-domain premise on the local factor. -/
lemma reference_matrix_commute (operator : HilbertOperator Local)
    (reference : HilbertOperator Reference) :
    referenceLift Reference operator * referenceAction Local reference =
      referenceAction Local reference * referenceLift Reference operator := by
  ext row column
  change (∑ entry : Local.Index × Reference.Index,
      (operator row.1 entry.1 * (if row.2 = entry.2 then (1 : Complex) else 0)) *
        ((if entry.1 = column.1 then 1 else 0) * reference entry.2 column.2)) =
    ∑ entry : Local.Index × Reference.Index,
      ((if row.1 = entry.1 then (1 : Complex) else 0) * reference row.2 entry.2) *
        (operator entry.1 column.1 * (if entry.2 = column.2 then 1 else 0))
  simpa [Fintype.sum_prod_type, mul_ite, ite_mul] using
    (mul_comm (operator row.1 column.1) (reference row.2 column.2))

private lemma commuting_conjugation {Index : Type} [Fintype Index]
    (left right matrix : Matrix Index Index Complex) (commute : left * right = right * left) :
    left * (right * matrix * right.conjTranspose) * left.conjTranspose =
      right * (left * matrix * left.conjTranspose) * right.conjTranspose := by
  have adjoint : right.conjTranspose * left.conjTranspose =
      left.conjTranspose * right.conjTranspose := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose commute
  calc
    _ = (left * right) * matrix * (right.conjTranspose * left.conjTranspose) := by
      simp only [Matrix.mul_assoc]
    _ = (right * left) * matrix * (left.conjTranspose * right.conjTranspose) := by
      rw [commute, adjoint]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- Full conjugation commutes with an arbitrary operator on the untouched reference. -/
lemma reference_conjugation (operator : HilbertOperator Local)
    (reference : HilbertOperator Reference)
    (matrix : HilbertOperator (Local.prod Reference)) :
    referenceLift Reference operator *
        (referenceAction Local reference * matrix *
          (referenceAction Local reference).conjTranspose) *
            (referenceLift Reference operator).conjTranspose =
      referenceAction Local reference *
        (referenceLift Reference operator * matrix *
          (referenceLift Reference operator).conjTranspose) *
            (referenceAction Local reference).conjTranspose :=
  commuting_conjugation _ _ _ (reference_matrix_commute operator reference)

/-- An actual complete local-Kraus equation gives naturality under any reference unitary. -/
lemma retained_referenceUnitary
    {Original Outcome Result : Type} [Fintype Original] [Fintype Outcome] [Fintype Result]
    (actual : ExecutionState Original (Local.prod Reference) →
      ExecutionState Result (Local.prod Reference))
    (record : Original → Outcome → Result)
    (operators : Original → Outcome → HilbertOperator Local)
    (blocks : ∀ state result,
      ((actual state).block result).matrix =
        ∑ original : Original, ∑ outcome : Outcome,
          if record original outcome = result then
            referenceLift Reference (operators original outcome) * (state.block original).matrix *
              (referenceLift Reference (operators original outcome)).conjTranspose
          else 0)
    (reference : UnitaryOperator Reference)
    (state : ExecutionState Original (Local.prod Reference)) :
    actual (state.applyUnitary
        (fun _ => UnitaryOperator.prodTensor (1 : UnitaryOperator Local) reference)) =
      (actual state).applyUnitary
        (fun _ => UnitaryOperator.prodTensor (1 : UnitaryOperator Local) reference) := by
  have referenceMatrix :
      (UnitaryOperator.prodTensor (1 : UnitaryOperator Local) reference :
        HilbertOperator (Local.prod Reference)) =
          referenceAction Local (reference : HilbertOperator Reference) := by
    ext row column
    rw [UnitaryOperator.unitaryOperator_prodTensor_apply]
    change (1 : HilbertOperator Local) row.1 column.1 * reference row.2 column.2 =
      (if row.1 = column.1 then (1 : Complex) else 0) * reference row.2 column.2
    by_cases same : row.1 = column.1
    · simp only [Matrix.one_apply, if_pos same]
    · simp only [Matrix.one_apply, if_neg same]
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  conv_rhs => rw [ExecutionState.applyUnitary_block, DensityOperator.applyUnitary_matrix]
  rw [blocks, blocks]
  simp only [ExecutionState.applyUnitary_block, DensityOperator.applyUnitary_matrix,
    referenceMatrix, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases selected : record original outcome = result
  · simp only [if_pos selected]
    exact reference_conjugation (operators original outcome)
      (reference : HilbertOperator Reference) (state.block original).matrix
  · simp only [if_neg selected, Matrix.mul_zero, Matrix.zero_mul]

end

end QuantumAlg.Execution.Instrument
