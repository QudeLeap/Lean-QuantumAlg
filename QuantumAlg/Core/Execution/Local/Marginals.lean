/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Reindex
public import QuantumAlg.Core.Base.Control.Operator
import all QuantumAlg.Core.Execution.Reference.Unitary
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Base.Control.Operator

/-!
# Local observations of actual joint inputs

Taking the reference marginal commutes with a local unitary and with the
finite sum of classical blocks. Exact basis relabeling also commutes with
unitary conjugation. These are the matrix and partial-trace rules
[dW19, qcnotes.tex:5381,5405,6827]; they preserve every local coherence and
make no assumption that the input is separated from its reference.
-/

namespace QuantumAlg

noncomputable section

namespace DensityOperator

theorem localUnitary_marginalLeft {R Reference : Register}
    (operator : UnitaryOperator R) (state : DensityOperator (Register.prod R Reference)) :
    (applyUnitary (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference))
      state).marginalLeft = applyUnitary operator state.marginalLeft := by
  have marginalMatrix : state.marginalLeft.matrix =
      ∑ reference : Reference.Index,
        state.matrix.submatrix (fun i => (i, reference)) (fun j => (j, reference)) := by
    ext row column
    rw [marginalLeft_matrix]
    simp only [Matrix.sum_apply, Matrix.submatrix_apply]
  apply DensityOperator.ext
  calc
    _ = ∑ reference : Reference.Index,
        (operator : HilbertOperator R) *
          state.matrix.submatrix (fun i => (i, reference)) (fun j => (j, reference)) *
            (operator : HilbertOperator R).conjTranspose := by
      ext row column
      rw [marginalLeft_matrix]
      simp only [Matrix.sum_apply]
      exact Finset.sum_congr rfl fun reference _ =>
        localUnitary_block operator state row column reference reference
    _ = (operator : HilbertOperator R) * state.marginalLeft.matrix *
        (operator : HilbertOperator R).conjTranspose := by
      rw [marginalMatrix, Matrix.mul_sum, Matrix.sum_mul]
    _ = _ := (applyUnitary_matrix operator state.marginalLeft).symm

public theorem applyUnitary_reindex {R S : Register} (operator : UnitaryOperator R)
    (state : DensityOperator R) (basisEquiv : R.Index ≃ S.Index) :
    (applyUnitary operator state).reindex basisEquiv =
      applyUnitary (UnitaryOperator.reindex basisEquiv operator) (state.reindex basisEquiv) := by
  apply DensityOperator.ext
  change (((operator : HilbertOperator R) * state.matrix *
      (operator : HilbertOperator R).conjTranspose).submatrix basisEquiv.symm basisEquiv.symm) =
    (operator : HilbertOperator R).submatrix basisEquiv.symm basisEquiv.symm *
      state.matrix.submatrix basisEquiv.symm basisEquiv.symm *
        ((operator : HilbertOperator R).submatrix basisEquiv.symm basisEquiv.symm).conjTranspose
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

end DensityOperator

namespace Execution.Input

theorem localState_quantumMarginal {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} (input : Input ctx Reference) :
    input.localState.quantumMarginal = input.state.quantumMarginal.marginalLeft := by
  apply DensityOperator.ext
  ext row column
  change (∑ value : Store ctx, (input.localState.block value).matrix) row column = _
  simp only [Matrix.sum_apply, localState_block_entry, DensityOperator.marginalLeft_matrix]
  change (∑ value : Store ctx, ∑ reference : Reference.Index,
    (input.state.block value).matrix (row, reference) (column, reference)) =
      ∑ reference : Reference.Index, (∑ value : Store ctx, (input.state.block value).matrix)
        (row, reference) (column, reference)
  simp only [Matrix.sum_apply]
  exact Finset.sum_comm

end Execution.Input

end

end QuantumAlg
