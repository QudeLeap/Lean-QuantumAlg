/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Selected.Store
import all QuantumAlg.Components.GateModel.Algorithm

/-!
# Actual native and selected-native blocks with concrete path carriers

These equations keep the native Unit path and the actual stored-value Sigma
path explicit. They avoid unfolding an unrelated dependent instruction family
when transporting complete original Store/history/reference blocks.
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Exact complete blocks of the actual native Unit-path instruction. -/
lemma native_matrix (program : UnitaryCircuit AlgorithmGate.model oracles ctx.quantumLayout)
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles operations
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History × Unit))) :
    (((Circuit.unitary (allowAllocation := false) (operations := operations)
      (classicalOracles := services) program).execute environment Reference state).block
      result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History),
        if (original.1, (original.2.1, (original.2.2, ()))) = result then
          let operator := UnitaryOperator.prodTensor (program.matrix environment.quantum)
            (1 : UnitaryOperator Reference)
          (operator : HilbertOperator (Register.prod ctx.register Reference)) *
            (state.block original).matrix *
              (operator : HilbertOperator (Register.prod ctx.register Reference)).conjTranspose
        else 0 := by
  let acted := state.applyUnitary fun _ =>
    UnitaryOperator.prodTensor (program.matrix environment.quantum) (1 : UnitaryOperator Reference)
  let update : Store ctx × (services.HiddenState × History) →
      Store ctx × (services.HiddenState × (History × Unit)) :=
    fun entry => (entry.1, (entry.2.1, (entry.2.2, ())))
  have actual : (Circuit.unitary (allowAllocation := false) (operations := operations)
      (classicalOracles := services) program).execute environment Reference state =
      acted.mapClassical update :=
    (Circuit.execute_unitary environment state program).trans
      (ExecutionState.executionState_mapClassical_congr acted rfl)
  refine (congrArg (fun final : State ctx Reference (services.HiddenState × (History × Unit)) =>
    (final.block result).matrix) actual).trans ?_
  have pushed := ExecutionState.mapClassical_block_matrix acted update result
  simpa only [acted, update, ExecutionState.applyUnitary_block,
    DensityOperator.applyUnitary_matrix] using pushed

/-- Exact selected-native blocks retain the actual value read from the caller Store. -/
lemma selected_matrix {shape : CShape} (input : CInputRef ctx shape)
    (program : shape.Value → UnitaryCircuit AlgorithmGate.model oracles ctx.quantumLayout)
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles operations
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History × (Σ _ : shape.Value, Unit)))) :
    (((Circuit.branch (model := .quantum AlgorithmGate.model oracles operations services)
      (shape := shape) (allowAllocation := false) input (fun value =>
      Circuit.unitary (operations := operations) (classicalOracles := services)
        (program value))).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History),
        if (original.1, (original.2.1, (original.2.2, ⟨original.1.read input, ()⟩))) =
            result then
          let operator := UnitaryOperator.prodTensor
            ((program (original.1.read input)).matrix environment.quantum)
            (1 : UnitaryOperator Reference)
          (operator : HilbertOperator (Register.prod ctx.register Reference)) *
            (state.block original).matrix *
              (operator : HilbertOperator (Register.prod ctx.register Reference)).conjTranspose
        else 0 := by
  let acted := state.applyUnitary fun entry => UnitaryOperator.prodTensor
    ((program (entry.1.read input)).matrix environment.quantum) (1 : UnitaryOperator Reference)
  let update : Store ctx × (services.HiddenState × History) →
      Store ctx × (services.HiddenState × (History × (Σ _ : shape.Value, Unit))) :=
    fun entry => (entry.1, (entry.2.1, (entry.2.2, ⟨entry.1.read input, ()⟩)))
  have actual : (Circuit.branch
      (model := .quantum AlgorithmGate.model oracles operations services) (shape := shape)
      (allowAllocation := false) input (fun value => Circuit.unitary (operations := operations)
        (classicalOracles := services) (program value))).execute environment Reference state =
      acted.mapClassical update :=
    (Circuit.selectedUnitary_execute input program environment state).trans
      (ExecutionState.executionState_mapClassical_congr acted rfl)
  refine (congrArg (fun final : State ctx Reference
    (services.HiddenState × (History × (Σ _ : shape.Value, Unit))) =>
      (final.block result).matrix) actual).trans ?_
  have pushed := ExecutionState.mapClassical_block_matrix acted update result
  simpa only [acted, update, ExecutionState.applyUnitary_block,
    DensityOperator.applyUnitary_matrix] using pushed

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
