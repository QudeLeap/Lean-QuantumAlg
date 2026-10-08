/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Arms
import all QuantumAlg.Components.Classical.NumberTheory.GCD.LexicalSemantics

/-!
# Exact execution of the accepted residue's native GCD arm

The accepted arm widens the preserved candidate, runs the expanded Euclidean
program in its actual temporary scopes, builds the comparison operand from
the stored default unit, and selects the real result arm. Its store equation
uses the actual GCD loop and path; no arithmetic classification instruction
or assumed scratch initialization replaces any part of the execution.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private def oneOp (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord (width + 1)) ctx ctx :=
  .wordResize width (width + 1) ctx
    (FirstAccepted.cellRead shared.selector.selected) scratch.extended

private def coprimeOp (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) :
    ClassicalOp (.product (.unsignedWord (width + 1)) (.unsignedWord (width + 1))) .bit ctx ctx :=
  .wordBinary .equal (width + 1) ctx
    (.product (FirstAccepted.cellRead gcdResult) (FirstAccepted.cellRead scratch.extended))
    scratch.positive

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

private def resultTail (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (oneOp shared scratch))
    (.seq (BitWord.instruction (execution := model) (coprimeOp scratch gcdResult))
      (chooseResult (model := model) shared scratch gcdResult))

private def resultTailStep (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    Store ctx × (resultTail (model := model) shared scratch gcdResult).Path :=
  let widened := BitWord.instructionStep (execution := model) (oneOp shared scratch) store
  let compared := BitWord.instructionStep (execution := model)
    (coprimeOp scratch gcdResult) widened.1
  let selected := resultStep (model := model) shared scratch gcdResult compared.1
  (selected.1, (widened.2, (compared.2, selected.2)))

private theorem resultTail_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (resultTail (model := model) shared scratch gcdResult).execute Reference state =
      state.mapClassical (fun entry =>
        let result := resultTailStep (model := model) shared scratch gcdResult entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  simp only [resultTail, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    decisionResult_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private def gcdTail (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) : Circuit model ctx ctx :=
  .seq (NumberTheory.GCD.lexicalBody (model := model)
    (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult)
    (resultTail (model := model) shared scratch gcdResult)

private def gcdTailStep (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    Store ctx × (gcdTail (model := model) shared scratch gcdResult).Path :=
  let reduced := NumberTheory.GCD.lexicalStep (model := model)
    (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult store
  let selected := resultTailStep (model := model) shared scratch gcdResult reduced.1
  (selected.1, (reduced.2, selected.2))

private theorem gcdTail_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (gcdTail (model := model) shared scratch gcdResult).execute Reference state =
      state.mapClassical (fun entry =>
        let result := gcdTailStep (model := model) shared scratch gcdResult entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical _ (resultTail (model := model) shared scratch gcdResult)
    (fun entry =>
      let result := NumberTheory.GCD.lexicalStep (model := model)
        (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult entry.1
      ((result.1, entry.2), result.2))
    (fun entry =>
      let result := resultTailStep (model := model) shared scratch gcdResult entry.1
      ((result.1, entry.2), result.2))
    (NumberTheory.GCD.gcdLexical_execute
      (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult)
    (resultTail_execute shared scratch gcdResult) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Exact store and path of widening, the actual Euclidean scopes, and the stored result arm. -/
def acceptedStep (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    Store ctx × (acceptedBody (model := model) shared scratch gcdResult).Path :=
  let widened := BitWord.instructionStep (execution := model) (Proposal.extendOp scratch) store
  let selected := gcdTailStep (model := model) shared scratch gcdResult widened.1
  (selected.1, (widened.2, selected.2))

/-- The full accepted arm executes its real GCD path and preserves all joint matrix blocks. -/
theorem decisionAccepted_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (acceptedBody (model := model) shared scratch gcdResult).execute Reference state =
      state.mapClassical (fun entry =>
        let result := acceptedStep (model := model) shared scratch gcdResult entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (BitWord.instruction (execution := model) (Proposal.extendOp scratch))
    (gcdTail (model := model) shared scratch gcdResult)
    (fun entry =>
      let result := BitWord.instructionStep (execution := model) (Proposal.extendOp scratch) entry.1
      ((result.1, entry.2), result.2))
    (fun entry =>
      let result := gcdTailStep (model := model) shared scratch gcdResult entry.1
      ((result.1, entry.2), result.2))
    (fun reference {_} _ initial =>
      (BitWord.bitWord_instruction_execute (Proposal.extendOp scratch)
        (Reference := reference) initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl))
    (gcdTail_execute shared scratch gcdResult) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
