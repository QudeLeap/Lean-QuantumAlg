/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.GCD
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Initialization

/-!
# Exact execution of the complete residue preparation decision

The equation composes the real initialization, stored acceptance branch,
expanded GCD arm, and final parameter write. It records the actual selected
path and preserves every complete quantum-reference matrix block. The store
map is obtained from those instructions on arbitrary incoming storage.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

private def acceptanceChoiceStep (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (value : CShape.Value .bit)
    (store : Store ctx) : Store ctx ×
      (if value.toBool then acceptedBody (model := model) shared scratch gcdResult
        else BitWord.instruction (execution := model) (clearWordOp scratch.candidate)).Path :=
  match value with
  | .bit false => BitWord.instructionStep (execution := model)
      (clearWordOp scratch.candidate) store
  | .bit true => acceptedStep (model := model) shared scratch gcdResult store

private lemma acceptanceChoice_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (value : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (if value.toBool then acceptedBody (model := model) shared scratch gcdResult
      else BitWord.instruction (execution := model) (clearWordOp scratch.candidate)).execute
        environment Reference state =
        state.mapClassical (fun entry =>
          let result := acceptanceChoiceStep (model := model) shared scratch gcdResult value entry.1
          (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  cases value with
  | bit bit =>
      cases bit
      · simp only [CShape.Value.toBool, acceptanceChoiceStep]
        refine (BitWord.bitWord_instruction_execute (environment := environment)
          (clearWordOp scratch.candidate) (Reference := Reference) state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl
      · simp only [CShape.Value.toBool, acceptanceChoiceStep]
        refine (decisionAccepted_execute shared scratch gcdResult Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual acceptance cell selects the computed GCD arm or one real payload-clearing write. -/
def acceptanceStep (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    Store ctx × (chooseAccepted (model := model) shared scratch gcdResult).Path :=
  let value := store.read (FirstAccepted.cellRead shared.selector.accepted)
  let selected := acceptanceChoiceStep (model := model) shared scratch gcdResult value store
  (selected.1, ⟨value, selected.2⟩)

/-- Actual stored acceptance controls the full selected matrix-preserving execution. -/
lemma decisionAcceptance_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (chooseAccepted (model := model) shared scratch gcdResult).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := acceptanceStep (model := model) shared scratch gcdResult entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_branch_mapClassical (environment := environment)
    (FirstAccepted.cellRead shared.selector.accepted) _
    (fun value before =>
      let result := acceptanceChoiceStep (model := model) shared scratch gcdResult value before.1
      ((result.1, before.2), result.2))
    (fun value reference history _ initial =>
      (acceptanceChoice_execute shared scratch gcdResult value reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Forgetting the real branch path exposes exactly the store selected by the acceptance bit. -/
lemma decisionAcceptance_store (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    (acceptanceStep (model := model) shared scratch gcdResult store).1 =
      if (store.read (FirstAccepted.cellRead shared.selector.accepted)).toBool then
        (acceptedStep (model := model) shared scratch gcdResult store).1
      else store.applyOp (clearWordOp scratch.candidate) := by
  cases value : store.read (FirstAccepted.cellRead shared.selector.accepted) with
  | bit bit =>
      dsimp only [acceptanceStep]
      rw [value]
      cases bit <;> rfl

private def packedTailStep (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width)) (store : Store ctx) :
    Store ctx × (Circuit.seq (chooseAccepted (model := model) shared scratch gcdResult)
      (BitWord.instruction (execution := model) (packOp shared scratch output))).Path :=
  let selected := acceptanceStep (model := model) shared scratch gcdResult store
  let packed := BitWord.instructionStep (execution := model)
    (packOp shared scratch output) selected.1
  (packed.1, (selected.2, packed.2))

private lemma packedTail_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (chooseAccepted (model := model) shared scratch gcdResult)
      (BitWord.instruction (execution := model) (packOp shared scratch output))).execute
        environment Reference state =
        state.mapClassical (fun entry =>
          let result := packedTailStep (model := model) shared scratch gcdResult output entry.1
          (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (chooseAccepted (model := model) shared scratch gcdResult)
    (BitWord.instruction (execution := model) (packOp shared scratch output))
    (fun entry =>
      let result := acceptanceStep (model := model) shared scratch gcdResult entry.1
      ((result.1, entry.2), result.2))
    (fun entry =>
      let result := BitWord.instructionStep (execution := model)
        (packOp shared scratch output) entry.1
      ((result.1, entry.2), result.2))
    (decisionAcceptance_execute shared scratch gcdResult)
    (fun reference {_} _ initial =>
      (BitWord.bitWord_instruction_execute (environment := environment)
        (packOp shared scratch output)
        (Reference := reference) initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl))
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Store and actual nested instruction path of the complete decision and parameter write. -/
def step (shared : Proposal.SharedRefs ctx width) (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width)) (store : Store ctx) :
    Store ctx × (circuit (model := model) shared scratch gcdResult output).Path :=
  let initialized := initializationStep (model := model) shared scratch store
  let final := packedTailStep (model := model) shared scratch gcdResult output initialized.1
  (final.1, (initialized.2, final.2))

/-- The complete decision preserves every reference correlation under its exact store map. -/
lemma decision_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (ParameterShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (circuit (model := model) shared scratch gcdResult output).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := step (model := model) shared scratch gcdResult output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (initializeBody (model := model) shared scratch) _
    (fun entry =>
      let result := initializationStep (model := model) shared scratch entry.1
      ((result.1, entry.2), result.2))
    (fun entry =>
      let result := packedTailStep (model := model) shared scratch gcdResult output entry.1
      ((result.1, entry.2), result.2))
    (decisionInitialization_execute shared scratch)
    (packedTail_execute shared scratch gcdResult output) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
