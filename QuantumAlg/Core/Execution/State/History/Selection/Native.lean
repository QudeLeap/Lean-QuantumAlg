/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.State.History.Selection
import all QuantumAlg.Core.Execution.State.History
import all QuantumAlg.Core.Execution.Circuit.Reference
import all QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.Classical.Step

/-!
# Complete history selection through stochastic steps and physical coordinates

Each identity retains the full density block, including every stored value and
off-diagonal reference entry. Selection is mathematical conditioning without
normalization; it adds no instruction, allocation or state assumption.
-/

namespace QuantumAlg

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace ExecutionState

/-- Stochastic sampling retains exactly the selected original complete blocks. -/
lemma selectClassical_kernelChoice {C Outcome D : Type}
    [Fintype C] [Fintype Outcome] [DecidableEq D] {R : Register}
    (state : ExecutionState C R) (transition : C → PMF Outcome)
    (read : C → D) (selected : D) :
    (kernelChoice state transition).selectClassical (fun record => read record.1) selected =
      kernelChoice (state.selectClassical read selected) transition := by
  apply ExecutionState.ext
  rintro ⟨value, outcome⟩
  apply DensityOperator.ext
  by_cases same : read value = selected
  · simp only [selectClassical_block, same, if_true, kernelChoice_block_matrix]
  · simp only [selectClassical_block, same, if_false, kernelChoice_block_matrix,
      DensityOperator.zero_matrix, smul_zero]

/-- Joint classical and quantum coordinates preserve the corresponding complete fiber. -/
lemma selectClassical_coordinate_transport {C K D : Type}
    [Fintype C] [Fintype K] [DecidableEq D] {R S : Register}
    (state : ExecutionState C R) (labels : C ≃ K) (basis : R.Index ≃ S.Index)
    (read : K → D) (selected : D) :
    ((state.mapClassical labels).reindex basis).selectClassical read selected =
      ((state.selectClassical (read ∘ labels) selected).mapClassical labels).reindex basis := by
  rw [reference_select, mapClassical_selectClassical]

end ExecutionState

namespace Execution.State

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {H D : Type} [Fintype H] [DecidableEq D]

/-- Native reads, sampling and real store writes preserve each earlier-history fiber. -/
lemma selectHistory_nativeStep {model : ClassicalOpModel}
    (application : model.Application ctx) (state : State ctx Reference H)
    (read : H → D) (selected : D) :
    (nativeStep application state).selectHistory (fun record => read record.1) selected =
      nativeStep application (state.selectHistory read selected) := by
  dsimp only [nativeStep, selectHistory]
  rw [ExecutionState.mapClassical_selectClassical]
  change ((kernelChoice state _).selectClassical
    (fun record => read record.1.2) selected).mapClassical _ = _
  exact congrArg
    (fun original : ExecutionState
        ((Store ctx × H) × (model.outputShape application.token).Value)
        (Register.prod ctx.register Reference) =>
      original.mapClassical (fun entry =>
        (entry.1.1.write application.output entry.2, (entry.1.2, entry.2))))
    (ExecutionState.selectClassical_kernelChoice state
      (fun entry => model.evaluate application.token (entry.1.read application.input))
      (fun entry => read entry.2) selected)

/-- A query may change its service state while preserving the selected earlier history. -/
lemma selectHistory_queryStep {model : ClassicalOracleModel}
    (environment : model.Interpretation)
    (application : model.Application ctx)
    (state : State ctx Reference (model.HiddenState × H)) (read : H → D) (selected : D) :
    (queryStep environment application state).selectHistory
      (fun record => read record.2.1) selected =
      queryStep environment application (state.selectHistory
        (fun record => read record.2) selected) := by
  dsimp only [queryStep, selectHistory]
  rw [ExecutionState.mapClassical_selectClassical]
  change ((kernelChoice state _).selectClassical
    (fun record => read record.1.2.2) selected).mapClassical _ = _
  exact congrArg
    (fun original : ExecutionState
        ((Store ctx × (model.HiddenState × H)) ×
          (model.HiddenState × (model.outputShape application.query).Value))
        (Register.prod ctx.register Reference) =>
      original.mapClassical (fun entry =>
        (entry.1.1.write application.output entry.2.2,
          (entry.2.1, (entry.1.2.2, entry.2.2)))))
    (ExecutionState.selectClassical_kernelChoice state
      (fun entry => model.transition environment application.query entry.2.1
        (entry.1.read application.input))
      (fun entry => read entry.2.2) selected)

end Execution.State

namespace ContextEmbedding

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller) {Reference : Register}
  {H D : Type} [Fintype H] [DecidableEq D]

/-- Splitting leaves the entire complement store outside the selected history coordinate. -/
lemma split_selectHistory (state : State caller Reference H)
    (read : H → D) (selected : D) :
    (placement.split state).selectHistory (fun record => read record.2) selected =
      placement.split (state.selectHistory read selected) := by
  dsimp only [split, State.selectHistory]
  rw [State.mapClassical_decision _ (Classical.decEq _) state (placement.record H),
    State.mapClassical_decision _ (Classical.decEq _)
      (state.selectClassical (fun record => read record.2) selected) (placement.record H)]
  exact ExecutionState.selectClassical_coordinate_transport state (placement.record H)
    (placement.referenceBasis Reference) (fun record => read record.2.2) selected

/-- Rejoining restores the full caller state without changing its selected history. -/
lemma join_selectHistory
    (state : State localCtx (Register.prod placement.frame.register Reference)
      (Store placement.frame × H)) (read : H → D) (selected : D) :
    (placement.join state).selectHistory read selected =
      placement.join (state.selectHistory (fun record => read record.2) selected) := by
  dsimp only [join, State.selectHistory]
  rw [State.mapClassical_decision _ (Classical.decEq _) state (placement.record H).symm,
    State.mapClassical_decision _ (Classical.decEq _)
      (state.selectClassical (fun record => read record.2.2) selected) (placement.record H).symm]
  exact ExecutionState.selectClassical_coordinate_transport state (placement.record H).symm
    (placement.referenceBasis Reference).symm (fun record => read record.2) selected

end ContextEmbedding

end

end QuantumAlg
