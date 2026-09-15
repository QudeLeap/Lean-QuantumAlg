/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Selected.Unitary
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.MarginalLaws

/-!
# Actual selected unitaries on complete stored-value blocks

The interpreter reads the real classical operand and records that selected
branch in its finite path. Each complete original store keeps its own quantum
and reference block, conjugated by precisely the selected program. The
equations below derive this from the same branch and unitary interpreter;
there is no second execution definition or supplied state transformation.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {shape : CShape}

/-- The actual selected operation conjugates each block
and records that same stored-value branch. -/
theorem selectedUnitary_execute (input : CInputRef ctx shape)
    (program : shape.Value → UnitaryCircuit ctx.register)
    (placed : ∀ value, (program value).physical_idx = ctx.physicalIdx)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    ((Circuit.branch input (fun value => .unitary (program value) (placed value))).execute
      Reference state) =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (program (entry.1.read input)).matrix (1 : UnitaryOperator Reference)).mapClassical
          (fun entry => (entry.1, (entry.2, ⟨entry.1.read input, ()⟩))) := by
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  rw [execute_branch_block_matrix]
  simp only [execute_unitary, State.unitary, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  simp only [ExecutionState.mapClassical_block_matrix, ExecutionState.applyUnitary_block]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro entry _
  rw [Finset.sum_eq_single (entry.1.read input)]
  · simp only [ExecutionState.selectClassical_block, if_true]
  · intro value _ different
    rw [ExecutionState.selectClassical_block, if_neg (Ne.symm different)]
    simp only [DensityOperator.applyUnitary_matrix, DensityOperator.zero_matrix,
      Matrix.mul_zero, Matrix.zero_mul, ite_self]
  · intro absent
    exact False.elim (absent (Finset.mem_univ _))

/-- One complete actual store selects one exact unitary on its full reference-correlated block. -/
theorem selectedUnitary_store_matrix (input : CInputRef ctx shape)
    (program : shape.Value → UnitaryCircuit ctx.register)
    (placed : ∀ value, (program value).physical_idx = ctx.physicalIdx)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (original : Store ctx) :
    (ExecutionState.filterClassical
      ((Circuit.branch input (fun value => .unitary (program value) (placed value))).execute
        Reference state) (fun entry => entry.1 = original)).quantumMarginal.matrix =
      (DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (program (original.read input)).matrix
          (1 : UnitaryOperator Reference))
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal).matrix := by
  let code := Circuit.branch input (fun value => .unitary (program value) (placed value))
  let update : Store ctx × History → Store ctx × (History × code.Path) :=
    fun entry => (entry.1, (entry.2, ⟨entry.1.read input, ()⟩))
  let acted := state.applyUnitary fun entry => UnitaryOperator.prodTensor
    (program (entry.1.read input)).matrix (1 : UnitaryOperator Reference)
  have executed := congrArg
    (fun result : State ctx Reference (History × code.Path) =>
      ((result.mapClassical (fun entry => entry.1)).block original).matrix)
    (selectedUnitary_execute input program placed state)
  have composition := congrArg
    (fun result : ExecutionState (Store ctx) (Register.prod ctx.register Reference) =>
      (result.block original).matrix)
    (ExecutionState.executionState_mapClassical_comp acted update (fun entry => entry.1))
  refine (BasisSeeded.store_matrix (code.execute Reference state) original).symm.trans
    (executed.trans (composition.trans ?_))
  let part := state.filterClassical (fun entry => entry.1 = original)
  let chosen := UnitaryOperator.prodTensor (program (original.read input)).matrix
    (1 : UnitaryOperator Reference)
  have fixed :
      (∑ entry : Store ctx × History,
        if entry.1 = original then (acted.block entry).matrix else 0) =
        ∑ entry : Store ctx × History,
          (DensityOperator.applyUnitary chosen (part.block entry)).matrix := by
    apply Finset.sum_congr rfl
    intro entry _
    by_cases same : entry.1 = original
    · simp only [acted, ExecutionState.applyUnitary_block, part,
        ExecutionState.filterClassical_block, same, if_true, chosen]
    · simp only [part, ExecutionState.filterClassical_block, same, if_false,
        DensityOperator.applyUnitary_matrix, DensityOperator.zero_matrix,
        Matrix.mul_zero, Matrix.zero_mul]
  exact fixed.trans (congrArg DensityOperator.matrix
    (ExecutionState.fixedUnitary_quantumMarginal part chosen))

end

end QuantumAlg.Circuit
