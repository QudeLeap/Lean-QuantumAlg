/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Execution.Random.Kernel.Point
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Complete deterministic composition inside the selected execution model

These laws compose already-proved equations of actual circuits. Each proved
step includes its real store and persistent service state. The mathematical
history is retained independently; a deterministic service transition may
change the hidden state without resetting or reinitializing it.

The semantic equations grant no extra operations or resource witnesses.
-/

namespace QuantumAlg.Circuit

variable {allowAllocation : Bool}

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
  (environment : model.Environment)

/-- A proved point-valued native declaration gives the actual deterministic store update. -/
lemma execute_classical_mapClassical
    (application : model.classicalOperations.Application ctx)
    (compute : (model.classicalOperations.inputShape application.token).Value →
      (model.classicalOperations.outputShape application.token).Value)
    (declared : ∀ value,
      model.classicalOperations.evaluate application.token value = PMF.pure (compute value))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.classical (model := model) (allowAllocation := allowAllocation)
      application).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := compute (entry.1.read application.input)
        (entry.1.write application.output result, (entry.2.1, (entry.2.2, result)))) := by
  rw [execute_classical]
  simp_rw [declared]
  rw [kernelChoice_pure,
    ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Identity retains the real store and shared service state with its unique empty path. -/
lemma execute_id_mapClassical (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.id (model := model) (allowAllocation := allowAllocation) ctx).execute
      environment Reference state =
      state.mapClassical (fun entry => (entry.1, (entry.2.1, (entry.2.2, ())))) :=
  execute_id environment state

/-- Proved deterministic circuits compose on the actual intermediate store and service state. -/
lemma execute_seq_mapClassical
    (first second : Circuit model ctx ctx allowAllocation)
    (firstStep : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × first.Path)
    (secondStep : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × second.Path)
    (firstEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      first.execute environment Reference state = state.mapClassical (fun entry =>
        let result := firstStep (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (secondEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      second.execute environment Reference state = state.mapClassical (fun entry =>
        let result := secondStep (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq first second).execute environment Reference state =
      state.mapClassical (fun entry =>
        let left := firstStep (entry.1, entry.2.1)
        let right := secondStep left.1
        (right.1.1, (right.1.2, (entry.2.2, (left.2, right.2))))) := by
  rw [execute_seq, firstEquation, secondEquation]
  dsimp only [State.mapHistory]
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance),
    ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual stored values select the proved deterministic bodies, including their service updates. -/
lemma execute_branch_mapClassical {shape : CShape}
    (input : CInputRef ctx shape) (body : shape.Value → Circuit model ctx ctx allowAllocation)
    (step : (value : shape.Value) → Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (body value).Path)
    (bodyEquation : ∀ (value : shape.Value) (Reference : Register)
      {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (body value).execute environment Reference state = state.mapClassical (fun entry =>
        let result := step value (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.branch input body).execute environment Reference state =
      state.mapClassical (fun entry =>
        let selected := entry.1.read input
        let result := step selected (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, ⟨selected, result.2⟩)))) := by
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  rw [execute_branch_block_matrix]
  simp only [bodyEquation, State.mapHistory]
  simp_rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  simp only [ExecutionState.mapClassical_block_matrix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro entry _
  rw [Finset.sum_eq_single (entry.1.read input)]
  · simp only [ExecutionState.selectClassical_block, if_true, Function.comp_apply]
  · intro value _ different
    rw [ExecutionState.selectClassical_block, if_neg (Ne.symm different)]
    simp only [DensityOperator.zero_matrix, ite_self]
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

end

end QuantumAlg.Circuit
