/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Initialization

/-!
# Exact native unit and factor result arms

Each arm consists of its two actual closed instructions. The stored
coprimality bit chooses their genuine branch and path. These state equations
retain the entire incoming quantum-reference block and do not assume that
any operand, output field, or branch bit is already initialized.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Exact two-write store of the selected unit arm. -/
def unitStore (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width) (store : Store ctx) : Store ctx :=
  (store.applyOp (.wordUnary .copy width ctx (FirstAccepted.cellRead scratch.candidate)
    shared.selector.selected)).applyOp (clearWordOp scratch.candidate)

/-- Exact two-write store of the selected factor arm. -/
def factorStore (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) : Store ctx :=
  (store.applyOp (.wordResize (width + 1) width ctx (FirstAccepted.cellRead gcdResult)
    scratch.candidate)).applyOp
      (.bit .not ctx (FirstAccepted.cellRead scratch.eligible) scratch.eligible)

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Native outcomes of the unit-copy and payload-clear instructions. -/
def unitStep (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width) (store : Store ctx) :
    Store ctx × (unitBody (model := model) shared scratch).Path :=
  let copied := BitWord.instructionStep (execution := model) (.wordUnary .copy width ctx
    (FirstAccepted.cellRead scratch.candidate) shared.selector.selected) store
  let cleared := BitWord.instructionStep (execution := model)
    (clearWordOp scratch.candidate) copied.1
  (cleared.1, (copied.2, cleared.2))

/-- Native outcomes of the factor-resize and tag-negation instructions. -/
def factorStep (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    Store ctx × (factorBody (model := model) scratch gcdResult).Path :=
  let resized := BitWord.instructionStep (execution := model) (.wordResize (width + 1) width ctx
    (FirstAccepted.cellRead gcdResult) scratch.candidate) store
  let tagged := BitWord.instructionStep (execution := model)
    (.bit .not ctx (FirstAccepted.cellRead scratch.eligible) scratch.eligible) resized.1
  (tagged.1, (resized.2, tagged.2))

/-- Actual unit copying preserves every hidden-state and quantum-reference correlation. -/
theorem decisionUnit_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (unitBody (model := model) shared scratch).execute Reference state =
      state.mapClassical (fun entry =>
        let result := unitStep (model := model) shared scratch entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  simp only [unitBody, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual factor writes preserve every hidden-state and quantum-reference correlation. -/
theorem decisionFactor_execute (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (factorBody (model := model) scratch gcdResult).execute Reference state =
      state.mapClassical (fun entry =>
        let result := factorStep (model := model) scratch gcdResult entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  simp only [factorBody, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private def resultChoiceStep (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (value : CShape.Value .bit)
    (store : Store ctx) : Store ctx ×
      (if value.toBool then unitBody (model := model) shared scratch
        else factorBody (model := model) scratch gcdResult).Path :=
  match value with
  | .bit false => factorStep (model := model) scratch gcdResult store
  | .bit true => unitStep (model := model) shared scratch store

private theorem resultChoice_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (value : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (if value.toBool then unitBody (model := model) shared scratch
        else factorBody (model := model) scratch gcdResult).execute
      Reference state = state.mapClassical (fun entry =>
        let result := resultChoiceStep (model := model) shared scratch gcdResult value entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  cases value with
  | bit bit =>
      cases bit
      · simp only [CShape.Value.toBool, resultChoiceStep]
        refine (decisionFactor_execute scratch gcdResult Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl
      · simp only [CShape.Value.toBool, resultChoiceStep]
        refine (decisionUnit_execute shared scratch Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Store and real sigma path selected by the actual coprimality bit. -/
def resultStep (shared : Proposal.SharedRefs ctx width) (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    Store ctx × (chooseResult (model := model) shared scratch gcdResult).Path :=
  let value := store.read (FirstAccepted.cellRead scratch.positive)
  let selected := resultChoiceStep (model := model) shared scratch gcdResult value store
  (selected.1, ⟨value, selected.2⟩)

/-- Real stored-condition execution selects exactly the corresponding unit or factor store. -/
theorem decisionResult_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (chooseResult (model := model) shared scratch gcdResult).execute Reference state =
      state.mapClassical (fun entry =>
        let result := resultStep (model := model) shared scratch gcdResult entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_branch_mapClassical (FirstAccepted.cellRead scratch.positive) _
    (fun value before =>
      let result := resultChoiceStep (model := model) shared scratch gcdResult value before.1
      ((result.1, before.2), result.2))
    (fun value reference history _ initial =>
      (resultChoice_execute shared scratch gcdResult value reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual stored branch changes the store according to that same coprimality bit. -/
theorem decisionResult_store (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    (resultStep (model := model) shared scratch gcdResult store).1 =
      if (store.read (FirstAccepted.cellRead scratch.positive)).toBool then
        unitStore shared scratch store else factorStore scratch gcdResult store := by
  dsimp only [resultStep]
  cases value : store.read (FirstAccepted.cellRead scratch.positive) with
  | bit bit => cases bit <;> rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
