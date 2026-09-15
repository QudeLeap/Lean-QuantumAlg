/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Basis.Seeded

/-!
# The complete quantum marginal is the sum of actual stored blocks

Partitioning an execution state by its complete actual classical store
and summing those blocks preserves every quantum-reference matrix entry.
A common stored-block formula can therefore be summed without dropping
zero-probability outcomes or assuming a separable reference
[dW19, qcnotes.tex:5381,5394,5405].
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Summing every actual complete stored block gives the entire quantum-reference marginal. -/
theorem sum_store_matrices {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (∑ stored : Store ctx,
      (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix) =
      state.quantumMarginal.matrix := by
  have actual := congrArg DensityOperator.matrix
    (ExecutionState.mapClassical_quantumMarginal state (fun entry => entry.1))
  change (∑ stored : Store ctx, ((state.mapClassical (fun entry => entry.1)).block stored).matrix) =
    state.quantumMarginal.matrix at actual
  simpa only [BasisSeeded.store_matrix] using actual

/-- A normalized common matrix coefficient on every actual store reconstructs the full matrix. -/
theorem matrix_of_uniform_store_blocks {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (target : HilbertOperator (Register.prod ctx.register Reference)) (coefficient : ℂ)
    (normalized : (Fintype.card (Store ctx) : ℂ) * coefficient = 1)
    (blocks : ∀ stored : Store ctx,
      (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
        coefficient • target) :
    state.quantumMarginal.matrix = target := by
  rw [← sum_store_matrices state]
  simp only [blocks, Finset.sum_const, Finset.card_univ]
  rw [← smul_assoc, nsmul_eq_mul, normalized, one_smul]

end

end QuantumAlg.Execution
