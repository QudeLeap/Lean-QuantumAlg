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

/-- The actual unit-copy and payload-clear instructions preserve all joint matrix blocks. -/
theorem decisionUnit_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (unitBody shared scratch).execute Reference state = state.mapClassical (fun entry =>
      (unitStore shared scratch entry.1, (entry.2, ((), ())))) := by
  simp only [unitBody, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- The actual factor-resize and tag-negation instructions preserve all joint matrix blocks. -/
theorem decisionFactor_execute (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (factorBody scratch gcdResult).execute Reference state = state.mapClassical (fun entry =>
      (factorStore scratch gcdResult entry.1, (entry.2, ((), ())))) := by
  simp only [factorBody, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

private def resultChoiceStep (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (value : CShape.Value .bit)
    (store : Store ctx) : Store ctx ×
      (if value.toBool then unitBody shared scratch else factorBody scratch gcdResult).Path :=
  match value with
  | .bit false => (factorStore scratch gcdResult store, ((), ()))
  | .bit true => (unitStore shared scratch store, ((), ()))

private theorem resultChoice_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (value : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (if value.toBool then unitBody shared scratch else factorBody scratch gcdResult).execute
      Reference state = state.mapClassical (fun entry =>
        ((resultChoiceStep shared scratch gcdResult value entry.1).1,
          (entry.2, (resultChoiceStep shared scratch gcdResult value entry.1).2))) := by
  cases value with
  | bit bit =>
      cases bit
      · simp only [CShape.Value.toBool, resultChoiceStep]
        refine (decisionFactor_execute scratch gcdResult Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _
      · simp only [CShape.Value.toBool, resultChoiceStep]
        refine (decisionUnit_execute shared scratch Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _

/-- Store and real sigma path selected by the actual coprimality bit. -/
def resultStep (shared : Proposal.SharedRefs ctx width) (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    Store ctx × (chooseResult shared scratch gcdResult).Path :=
  let value := store.read (FirstAccepted.cellRead scratch.positive)
  let selected := resultChoiceStep shared scratch gcdResult value store
  (selected.1, ⟨value, selected.2⟩)

/-- Real stored-condition execution selects exactly the corresponding unit or factor store. -/
theorem decisionResult_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (chooseResult shared scratch gcdResult).execute Reference state =
      state.mapClassical (fun entry => ((resultStep shared scratch gcdResult entry.1).1,
        (entry.2, (resultStep shared scratch gcdResult entry.1).2))) := by
  exact Circuit.execute_branch_mapClassical (FirstAccepted.cellRead scratch.positive)
    (fun value => if value.toBool then unitBody shared scratch else factorBody scratch gcdResult)
    (resultChoiceStep shared scratch gcdResult) (resultChoice_execute shared scratch gcdResult)
    Reference state

/-- The actual stored branch changes the store according to that same coprimality bit. -/
theorem decisionResult_store (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    (resultStep shared scratch gcdResult store).1 =
      if (store.read (FirstAccepted.cellRead scratch.positive)).toBool then
        unitStore shared scratch store else factorStore scratch gcdResult store := by
  dsimp only [resultStep]
  cases value : store.read (FirstAccepted.cellRead scratch.positive) with
  | bit bit => cases bit <;> rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
