/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Interpret
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Unitary execution selected by an actual classical read

The single circuit interpreter first partitions the input by the stored value,
then executes the corresponding unitary body. Summing the resulting classical
blocks gives exactly one conjugation for each original block. Each operator
acts as the selected unitary tensored with the identity on an arbitrary
external reference [dW19, qcnotes.tex:5405].
-/

namespace QuantumAlg.Circuit

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem branch_quantumMarginal_matrix {kind : ProblemKind}
    {pre post : RuntimeCtx kind} {shape : CShape} (input : CInputRef pre shape)
    (body : shape.Value → Circuit pre post) {Reference : Register}
    {H : Type} [Fintype H] (state : State pre Reference H) :
    ((Circuit.branch input body).execute Reference state).quantumMarginal.matrix =
      ∑ value : shape.Value,
        ((body value).execute Reference
          (state.selectClassical (·.1.read input) value)).quantumMarginal.matrix := by
  change (∑ result,
    (((Circuit.branch input body).execute Reference state).block result).matrix) = _
  simp_rw [Circuit.execute_branch_block_matrix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro value _
  exact congrArg DensityOperator.matrix (State.mapHistory_quantumMarginal _ _)

/-- Internal state form of the stored-value selection law, used by concrete circuit proofs. -/
theorem selectedUnitary_quantumMarginal {ctx : RuntimeCtx .quantum} {shape : CShape}
    (input : CInputRef ctx shape) (program : shape.Value → UnitaryCircuit ctx.register)
    (placed : ∀ value, (program value).physical_idx = ctx.physicalIdx)
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H) :
    ((Circuit.branch input (fun value => Circuit.unitary (program value) (placed value))).execute
      Reference state).quantumMarginal =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (program (entry.1.read input)).matrix (1 : UnitaryOperator Reference)).quantumMarginal := by
  apply DensityOperator.ext
  rw [branch_quantumMarginal_matrix]
  simp only [Circuit.execute_unitary, State.unitary, ExecutionState.mapClassical_quantumMarginal]
  change (∑ choice : shape.Value, ∑ entry : Store ctx × H,
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (program choice).matrix (1 : UnitaryOperator Reference))
      ((state.selectClassical (fun value => value.1.read input) choice).block entry)).matrix) =
    ∑ entry : Store ctx × H,
      (DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (program (entry.1.read input)).matrix
          (1 : UnitaryOperator Reference)) (state.block entry)).matrix
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro entry _
  have selected (choice : shape.Value) :
      (DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (program choice).matrix (1 : UnitaryOperator Reference))
        ((state.selectClassical (fun value => value.1.read input) choice).block entry)).matrix =
      if entry.1.read input = choice then
        (DensityOperator.applyUnitary
          (UnitaryOperator.prodTensor (program choice).matrix (1 : UnitaryOperator Reference))
          (state.block entry)).matrix else 0 := by
    rw [ExecutionState.selectClassical_block]
    by_cases equal : entry.1.read input = choice
    · simp only [equal, if_true]
    · simp only [equal, if_false, DensityOperator.applyUnitary_matrix,
        DensityOperator.zero_matrix, Matrix.mul_zero, Matrix.zero_mul]
  simp_rw [selected]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The actual stored value selects each block's unitary. The full matrix retains
all correlations with the external reference. -/
public theorem circuit_selectedUnitary_quantumMarginal_matrix {ctx : RuntimeCtx .quantum}
    {shape : CShape} (input : CInputRef ctx shape)
    (program : shape.Value → UnitaryCircuit ctx.register)
    (placed : ∀ value, (program value).physical_idx = ctx.physicalIdx)
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H) :
    ((Circuit.branch input (fun value => Circuit.unitary (program value) (placed value))).execute
      Reference state).quantumMarginal.matrix =
      ∑ entry : Store ctx × H,
        (DensityOperator.applyUnitary
          (UnitaryOperator.prodTensor (program (entry.1.read input)).matrix
            (1 : UnitaryOperator Reference)) (state.block entry)).matrix :=
  congrArg DensityOperator.matrix (selectedUnitary_quantumMarginal input program placed state)

end

end QuantumAlg.Circuit
