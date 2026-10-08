/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Basis.Seeded.Record
import all QuantumAlg.Core.Execution.Basis.Seeded.Processing
import all QuantumAlg.Core.Execution.Input.Oracle

/-!
# Local input support admits every actual reference extension

The local caller and persistent-service blocks determine support at one fixed
physical basis label. Positivity transports their zero diagonals to every
joint reference row and column. Conversely, a real complete seeded execution
supplies precisely that local support after only histories are forgotten.
-/

namespace QuantumAlg.Execution.BasisSeeded

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Local block support supplies the full physical seed on every external reference extension. -/
theorem of_block_marginal_support {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {History : Type} [Fintype History]
    (seed : ctx.register.Index) (state : State ctx Reference History)
    (support : ∀ (entry : Store ctx × History) (basis : ctx.register.Index), basis ≠ seed →
      (state.block entry).marginalLeft.matrix basis basis = 0) : Holds seed state := by
  intro original left right leftRef rightRef
  by_cases supported : left = seed ∧ right = seed
  · obtain ⟨rfl, rfl⟩ := supported
    exact (if_pos ⟨rfl, rfl⟩).symm
  · refine Eq.trans ?_ (if_neg supported).symm
    have absent (entry : Store ctx × History) :
        (state.block entry).matrix (left, leftRef) (right, rightRef) = 0 := by
      by_cases leftSeed : left = seed
      · exact DensityOperator.joint_column_zero_of_marginal_diagonal_zero (state.block entry)
          right (support entry right (fun rightSeed => supported ⟨leftSeed, rightSeed⟩))
          rightRef (left, leftRef)
      · exact DensityOperator.joint_row_zero_of_marginal_diagonal_zero (state.block entry)
          left (support entry left leftSeed) leftRef (right, rightRef)
    have grouped := congrArg
      (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
        matrix (left, leftRef) (right, rightRef)) (store_matrix state original).symm
    refine grouped.trans ?_
    simp only [ExecutionState.mapClassical_block_matrix, Matrix.sum_apply, Matrix.ite_apply,
      absent, Matrix.zero_apply, ite_self, Finset.sum_const_zero]

/-- The genuine seeded state supplies the same local support in every complete original block. -/
theorem block_marginal_support {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {History : Type} [Fintype History]
    (seed : ctx.register.Index) (state : State ctx Reference History) (seeded : Holds seed state)
    (entry : Store ctx × History) (basis : ctx.register.Index) (outside : basis ≠ seed) :
    (state.block entry).marginalLeft.matrix basis basis = 0 := by
  rw [DensityOperator.marginalLeft_matrix]
  simp only [block_diagonal_zero seed state seeded entry basis outside, Finset.sum_const_zero]

/-- A local joint initialization predicate covers every actual oracle input reference extension. -/
theorem oracleInput_of_local_support {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    {Reference : Register} (seed : ctx.register.Index)
    (input : OracleInput model.classicalOracles ctx Reference)
    (support : ∀ (entry : Store ctx × model.HiddenState) (basis : ctx.register.Index),
      basis ≠ seed → (input.localState.block entry).matrix basis basis = 0) :
    Holds seed input.state :=
  of_block_marginal_support seed input.state support

end

end QuantumAlg.Execution.BasisSeeded
