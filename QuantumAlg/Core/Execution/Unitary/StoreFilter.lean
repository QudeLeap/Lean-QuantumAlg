/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measured.FeedForward
import all QuantumAlg.Core.Execution.MarginalLaws

/-!
# Actual unitary execution under a classical store observation

A unitary instruction leaves every classical cell unchanged. Any predicate
on those real cells therefore selects exactly the same original blocks,
with the unitary acting on their complete joint reference state
[dW19, qcnotes.tex:5381,5405].
-/

namespace QuantumAlg.Circuit

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Observing actual classical stores commutes with their same fixed local unitary instruction. -/
theorem unitary_store_filter {ctx : RuntimeCtx .quantum}
    (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (predicate : Store ctx → Prop)
    [DecidablePred predicate] :
    (ExecutionState.filterClassical
      ((Circuit.unitary (operations := operations) (classicalOracles := services)
        program).execute Reference state)
      (fun entry => predicate entry.1)).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference))
        (state.filterClassical (fun entry => predicate entry.1)).quantumMarginal := by
  let operator := UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference)
  let part := state.filterClassical (fun entry => predicate entry.1)
  apply DensityOperator.ext
  calc
    _ = ∑ original : Store ctx × (services.HiddenState × History),
        if predicate original.1 then
          (DensityOperator.applyUnitary operator (state.block original)).matrix else 0 := by
      ext left right
      rw [ExecutionState.filterClassical_matrix_weighted, Circuit.execute_unitary]
      refine (@ExecutionState.weightedMatrixEntry_mapClassical
        (Store ctx × (services.HiddenState × History))
        (Store ctx × (services.HiddenState × (History × Unit))) _ _ _ _
        (state.applyUnitary (fun _ => operator))
        (fun value => (value.1, (value.2.1, (value.2.2, ()))))
        (fun value => if predicate value.1 then (1 : ℂ) else 0) left right).trans ?_
      simp only [ExecutionState.weightedMatrixEntry,
        ExecutionState.applyUnitary_block, Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply,
        ite_mul, one_mul, zero_mul, operator]
    _ = ∑ original : Store ctx × (services.HiddenState × History),
        (DensityOperator.applyUnitary operator (part.block original)).matrix := by
      apply Finset.sum_congr rfl
      intro original _
      by_cases present : predicate original.1
      · simp only [part, ExecutionState.filterClassical_block, present, if_true]
      · simp only [part, ExecutionState.filterClassical_block, present, if_false,
          DensityOperator.applyUnitary_matrix, DensityOperator.zero_matrix,
          Matrix.mul_zero, Matrix.zero_mul]
    _ = _ := ExecutionState.executionState_sum_unitaryBlocks part operator

end

end QuantumAlg.Circuit
