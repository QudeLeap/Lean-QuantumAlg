/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Compositional matrix laws for an untouched external reference

These exact identities factor the same reference identity through a native
unitary or an ordered product of local Kraus matrices. Their algebraic proofs
are independent of any concrete circuit, context width or outcome history.
-/

namespace QuantumAlg

open scoped Kronecker

namespace HilbertOperator

/-- Two local factors retain their order beside the same unchanged reference. -/
lemma kronecker_identity_mul {Local Reference : Register}
    (left right : HilbertOperator Local) :
    (left ⊗ₖ (1 : HilbertOperator Reference)) *
        (right ⊗ₖ (1 : HilbertOperator Reference)) =
      (left * right) ⊗ₖ (1 : HilbertOperator Reference) := by
  simpa only [Matrix.one_mul] using
    (Matrix.mul_kronecker_mul left right
      (1 : HilbertOperator Reference) (1 : HilbertOperator Reference)).symm

/-- An arbitrary finite native/Kraus word needs only one reference factorization. -/
lemma kronecker_identity_list_prod {Local Reference : Register}
    (operators : List (HilbertOperator Local)) :
    (operators.map (fun operator => operator ⊗ₖ (1 : HilbertOperator Reference))).prod =
      operators.prod ⊗ₖ (1 : HilbertOperator Reference) := by
  induction operators with
  | nil => simp only [List.map_nil, List.prod_nil, Matrix.one_kronecker_one]
  | cons operator rest ih =>
      rw [List.map_cons, List.prod_cons, List.prod_cons, ih, kronecker_identity_mul]

/-- Reindex a local diagonal intertwining law while leaving the external reference intact. -/
lemma kronecker_identity_diagonal_transport {Source Target Reference : Register}
    (coordinates : Target.Index ≃ Source.Index) (operator : HilbertOperator Source)
    (before after : Source.Index → ℂ)
    (actual : operator * Matrix.diagonal before = Matrix.diagonal after * operator) :
    (operator.submatrix coordinates coordinates ⊗ₖ (1 : HilbertOperator Reference)) *
        Matrix.diagonal (fun entry => before (coordinates entry.1)) =
      Matrix.diagonal (fun entry => after (coordinates entry.1)) *
        (operator.submatrix coordinates coordinates ⊗ₖ (1 : HilbertOperator Reference)) := by
  ext row column
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have entry := congrArg (fun matrix : HilbertOperator Source =>
    matrix (coordinates row.1) (coordinates column.1)) actual
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at entry
  change (operator (coordinates row.1) (coordinates column.1) *
      (if row.2 = column.2 then (1 : ℂ) else 0)) * before (coordinates column.1) =
    after (coordinates row.1) *
      (operator (coordinates row.1) (coordinates column.1) *
        (if row.2 = column.2 then (1 : ℂ) else 0))
  by_cases same : row.2 = column.2
  · simpa only [if_pos same, mul_one] using entry
  · rw [if_neg same, mul_zero, zero_mul, mul_zero]

end HilbertOperator

/-- Coercing the actual tensor unitary keeps the same matrix identity on the reference. -/
lemma unitaryOperator_prodTensor_identity {Local Reference : Register}
    (operator : UnitaryOperator Local) :
    (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference) :
      HilbertOperator (Register.prod Local Reference)) =
      (operator : HilbertOperator Local) ⊗ₖ (1 : HilbertOperator Reference) := by
  ext row column
  rw [UnitaryOperator.unitaryOperator_prodTensor_apply]
  rfl

end QuantumAlg
