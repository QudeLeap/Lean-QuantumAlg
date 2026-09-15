/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Base.State.Normalized

/-!
# A pure basis promise from exact matrix support

The reset endpoint uses exact zero rows of its observed density operator to
establish a pure basis-state promise. Positivity supplies Hermitian symmetry;
the remaining diagonal coefficient is the original probability mass.
The target is the pure-state outer product [dW19, qcnotes.tex:5381], with no
division or normalization of an impossible observation.
-/

namespace QuantumAlg.StatePromise

noncomputable section

open scoped ComplexOrder

/-- A probability-bearing density operator supported on one basis label has
exactly that pure-state promise at its original mass. -/
public theorem statePromise_pureKet_of_row_support {R : Register}
    (state : DensityOperator R) (basis : R.Index)
    (support : ∀ row, row ≠ basis → ∀ column, state.matrix row column = 0) :
    (StatePromise.pure (NormalizedVector.ket basis)).Holds state := by
  have traceEq : state.matrix.trace = state.matrix basis basis := by
    change (∑ row : R.Index, state.matrix row row) = state.matrix basis basis
    apply Finset.sum_eq_single basis
    · intro row _ different
      exact support row different row
    · intro absent
      exact False.elim (absent (Finset.mem_univ basis))
  have diagonal : state.matrix basis basis = (state.mass : ℂ) := by
    apply Complex.ext
    · change (state.matrix basis basis).re = state.matrix.trace.re
      exact congrArg Complex.re traceEq.symm
    · exact (congrArg Complex.im traceEq.symm).trans state.trace_im_eq_zero
  have otherColumn (column : R.Index) (different : column ≠ basis) :
      state.matrix basis column = 0 := by
    rw [← state.positive.isHermitian.apply basis column, support column different basis]
    exact star_zero ℂ
  change state.matrix = (state.mass : ℝ) •
    (DensityOperator.ofPure (NormalizedVector.ket basis)).matrix
  ext row column
  change state.matrix row column = state.mass •
    (DensityOperator.ofPure (NormalizedVector.ket basis)).matrix row column
  rw [DensityOperator.ofPure_matrix]
  by_cases sameRow : row = basis <;> by_cases sameColumn : column = basis
  · subst row
    subst column
    simpa only [NormalizedVector.ket_apply, if_true, star_one, mul_one,
      Complex.real_smul] using diagonal
  · subst row
    simp only [otherColumn column sameColumn, NormalizedVector.ket_apply,
      if_neg sameColumn, star_zero, mul_zero, smul_zero]
  · simp only [support row sameRow column, NormalizedVector.ket_apply,
      if_neg sameRow, zero_mul, smul_zero]
  · simp only [support row sameRow column, NormalizedVector.ket_apply,
      if_neg sameRow, zero_mul, smul_zero]

end

end QuantumAlg.StatePromise
