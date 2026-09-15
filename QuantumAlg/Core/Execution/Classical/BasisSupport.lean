/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Base.State.Density.BasisSupport

/-!
# Classical observation preserves quantum basis support

Every actual classical block is positive. A basis coordinate absent from
their sum is absent from each block and from every predicate-selected sum.
The same fact holds for locally stated support on a complete joint state
with an arbitrary external reference [dW19, qcnotes.tex:5381,5394,6827].
-/

namespace QuantumAlg.ExecutionState

noncomputable section

open scoped ComplexOrder

variable {C : Type} [Fintype C] {R Reference : Register}

/-- A zero quantum-marginal diagonal forces the same diagonal to vanish in each actual block. -/
theorem block_diagonal_zero (state : ExecutionState C R) (basis : R.Index)
    (zero : state.quantumMarginal.matrix basis basis = 0) (value : C) :
    (state.block value).matrix basis basis = 0 := by
  classical
  have total : (∑ current : C, (state.block current).matrix basis basis) = 0 := by
    simpa only [quantumMarginal, Matrix.sum_apply] using zero
  have bound : (state.block value).matrix basis basis ≤
      ∑ current : C, (state.block current).matrix basis basis :=
    Finset.single_le_sum (fun current _ => (state.block current).positive.diag_nonneg)
      (Finset.mem_univ value)
  exact le_antisymm (bound.trans_eq total) (state.block value).positive.diag_nonneg

/-- Selecting actual classical blocks cannot introduce a previously absent basis coordinate. -/
theorem filterClassical_diagonal_zero (state : ExecutionState C R)
    (predicate : C → Prop) [DecidablePred predicate] (basis : R.Index)
    (zero : state.quantumMarginal.matrix basis basis = 0) :
    (state.filterClassical predicate).quantumMarginal.matrix basis basis = 0 := by
  change (∑ value : C, ((state.filterClassical predicate).block value).matrix) basis basis = 0
  rw [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro value _
  by_cases present : predicate value
  · simp only [filterClassical_block, present, if_true]
    exact block_diagonal_zero state basis zero value
  · simp only [filterClassical_block, present, if_false,
      DensityOperator.zero_matrix, Matrix.zero_apply]

/-- Locally stated support remains valid in every selected full reference-correlated state. -/
theorem filterClassical_local_diagonal_zero
    (state : ExecutionState C (Register.prod R Reference))
    (predicate : C → Prop) [DecidablePred predicate] (basis : R.Index)
    (zero : state.quantumMarginal.marginalLeft.matrix basis basis = 0) :
    (state.filterClassical predicate).quantumMarginal.marginalLeft.matrix basis basis = 0 := by
  rw [DensityOperator.marginalLeft_matrix]
  apply Finset.sum_eq_zero
  intro reference _
  exact filterClassical_diagonal_zero state predicate (basis, reference)
    (DensityOperator.joint_diagonal_zero_of_marginal_diagonal_zero
      state.quantumMarginal basis zero reference)

end

end QuantumAlg.ExecutionState
