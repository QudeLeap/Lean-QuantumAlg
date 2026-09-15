/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Complete state equations for deterministic classical composition

These laws compose equations already proved about the actual circuit
interpreter. The selected branch is determined by its real storage reference.
Every equation keeps each entire quantum-reference matrix block, including
mixed states and correlations, while recording the actual instruction paths.
There is no second instruction language or alternative resource interpretation.
-/

namespace QuantumAlg.ExecutionState

/-- Every matrix entry of a deterministic classical map is the sum of its actual input fiber. -/
theorem mapClassical_block_matrix {C D : Type} [Fintype C] [Fintype D]
    [DecidableEq D] {R : Register} (state : ExecutionState C R) (update : C → D)
    (result : D) :
    ((state.mapClassical update).block result).matrix =
      ∑ entry : C, if update entry = result then (state.block entry).matrix else 0 := rfl

end QuantumAlg.ExecutionState

namespace QuantumAlg.Circuit

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- An atomic closed classical operation maps its actual store and records its unique path. -/
theorem execute_classical_mapClassical {input output : CShape}
    (op : ClassicalOp input output ctx ctx) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.classical op).execute Reference state =
      state.mapClassical (fun entry => (entry.1.applyOp op, (entry.2, ()))) := rfl

/-- Identity preserves the real store and attaches only its unique empty path. -/
theorem execute_id_mapClassical (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.id ctx).execute Reference state =
      state.mapClassical (fun entry => (entry.1, (entry.2, ()))) := by
  rw [execute_id]
  simp only [State.skip, State.mapHistory]
  congr 1
  exact Subsingleton.elim _ _

/-- Two proved deterministic circuit equations compose on their actual intermediate store. -/
theorem execute_seq_mapClassical
    (first second : Circuit ctx ctx)
    (firstStep : Store ctx → Store ctx × first.Path)
    (secondStep : Store ctx → Store ctx × second.Path)
    (firstEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      first.execute Reference state = state.mapClassical (fun entry =>
        ((firstStep entry.1).1, (entry.2, (firstStep entry.1).2))))
    (secondEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      second.execute Reference state = state.mapClassical (fun entry =>
        ((secondStep entry.1).1, (entry.2, (secondStep entry.1).2))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.seq first second).execute Reference state =
      state.mapClassical (fun entry =>
        ((secondStep (firstStep entry.1).1).1,
          (entry.2, ((firstStep entry.1).2, (secondStep (firstStep entry.1).1).2)))) := by
  simp only [execute_seq, firstEquation, secondEquation, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- A conditional composes the exact body equations using the value read from
the incoming store. Every resulting block retains its original full matrix. -/
theorem execute_branch_mapClassical {shape : CShape}
    (input : CInputRef ctx shape) (body : shape.Value → Circuit ctx ctx)
    (step : (value : shape.Value) → Store ctx → Store ctx × (body value).Path)
    (bodyEquation : ∀ (value : shape.Value) (Reference : Register)
      {History : Type} [Fintype History] (state : State ctx Reference History),
      (body value).execute Reference state = state.mapClassical (fun entry =>
        ((step value entry.1).1, (entry.2, (step value entry.1).2))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.branch input body).execute Reference state =
      state.mapClassical (fun entry =>
        ((step (entry.1.read input) entry.1).1,
          (entry.2, ⟨entry.1.read input, (step (entry.1.read input) entry.1).2⟩))) := by
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  rw [execute_branch_block_matrix]
  simp only [bodyEquation, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  simp only [ExecutionState.mapClassical_block_matrix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro entry _
  rw [Finset.sum_eq_single (entry.1.read input)]
  · simp only [ExecutionState.selectClassical_block, if_true]
  · intro value _ different
    rw [ExecutionState.selectClassical_block, if_neg (Ne.symm different)]
    simp only [DensityOperator.zero_matrix, ite_self]
  · intro absent
    exact False.elim (absent (Finset.mem_univ _))

end

end QuantumAlg.Circuit
