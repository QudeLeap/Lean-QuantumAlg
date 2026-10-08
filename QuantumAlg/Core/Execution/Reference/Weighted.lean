/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reference.Unitary
import all QuantumAlg.Core.Execution.Measurement.Fibers

/-!
# Classical weights beside local unitary execution

Every classical block has its own full reference matrix. A local unitary,
including one selected by that block, preserves its weighted partial trace.
The weight may be complex and no normalization or independence is assumed.
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace ExecutionState

/-- A classically selected local unitary preserves every weighted reference entry. -/
theorem referenceFiberSum_applyLocalUnitary {C : Type} [Fintype C] {R Reference : Register}
    (state : ExecutionState C (Register.prod R Reference)) (program : C → UnitaryOperator R)
    (weight : C → ℂ) (left right : Reference.Index) :
    referenceFiberSum (state.applyUnitary (fun value =>
      UnitaryOperator.prodTensor (program value) (1 : UnitaryOperator Reference)))
        (fun value _ => weight value) left right =
      referenceFiberSum state (fun value _ => weight value) left right := by
  unfold referenceFiberSum
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro value _
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact congrArg (fun coefficient : ℂ => weight value * coefficient)
    (DensityOperator.localUnitary_reference_entry (program value) (state.block value) left right)

end ExecutionState

namespace Circuit

open Execution

/-- The actual unitary instruction preserves each complete store-weighted reference entry. -/
theorem unitary_weighted_reference {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    {ctx : RuntimeCtx .quantum} (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (classicalOracles.HiddenState × History))
    (weight : Store ctx → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((Circuit.unitary (operations := operations)
        (classicalOracles := classicalOracles) program).execute Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state (fun entry _ => weight entry.1) left right := by
  rw [execute_unitary]
  simp only [ExecutionState.referenceFiberSum_mapClassical]
  exact ExecutionState.referenceFiberSum_applyLocalUnitary state (fun _ => program.matrix)
    (fun entry => weight entry.1) left right

end Circuit

end

end QuantumAlg
