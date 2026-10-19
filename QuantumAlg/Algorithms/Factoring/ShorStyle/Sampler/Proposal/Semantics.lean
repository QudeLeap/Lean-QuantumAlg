/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal
import all QuantumAlg.Components.Classical.TerminalDecode.FoldSemantics
import all QuantumAlg.Components.Classical.FirstAccepted.Semantics

/-!
# Complete block equations for actual proposal scanning

These equations compose the genuine decoder, comparison instructions and
stored-condition selector. Every mathematical update records the path of
those same circuits, while retaining every incoming quantum-reference matrix
block. The finite fold follows the original proposal order at every width.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width count : Nat}

/-- The exact store obtained by the four native comparison instructions. -/
def comparisonStore (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (store : Store ctx) : Store ctx :=
  (((store.applyOp (extendOp scratch)).applyOp (positiveOp shared scratch)).applyOp
    (belowOp shared scratch)).applyOp (eligibleOp scratch)

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The four actual result values form the comparison suffix's native path. -/
def comparisonStep (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (store : Store ctx) : Store ctx × (comparisonBody (model := model) shared scratch).Path :=
  let extended := BitWord.instructionStep (execution := model) (extendOp scratch) store
  let positive := BitWord.instructionStep (execution := model)
    (positiveOp shared scratch) extended.1
  let below := BitWord.instructionStep (execution := model) (belowOp shared scratch) positive.1
  let eligible := BitWord.instructionStep (execution := model) (eligibleOp scratch) below.1
  (eligible.1, (extended.2, (positive.2, (below.2, eligible.2))))

/-- Recording actual native outcomes leaves the original comparison store equation exact. -/
lemma proposalComparison_step_store (shared : SharedRefs ctx width)
    (scratch : ScratchRefs ctx width) (store : Store ctx) :
    (comparisonStep (model := model) shared scratch store).1 =
      comparisonStore shared scratch store := rfl

/-- The actual comparison suffix preserves each complete quantum-reference block. -/
lemma proposalComparison_execute (shared : SharedRefs ctx width)
    (scratch : ScratchRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (comparisonBody (model := model) shared scratch).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := comparisonStep (model := model) shared scratch entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  simp only [comparisonBody, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The decoder's exact store and path on the addressed packed proposal. -/
def decodedStep (sample : CInputRef ctx (.bits (count * width))) (proposal : Fin count)
    (scratch : ScratchRefs ctx width) (store : Store ctx) :
    Store ctx × (TerminalDecode.intoFromBitRefs (model := model) .littleEndian
      (PackedSample.proposalRefs sample proposal) scratch.candidate).Path :=
  TerminalDecode.foldStep (model := model) scratch.candidate
    (List.ofFn (fun index => PackedSample.proposalRefs sample proposal
      (TerminalDecode.sourceIndex .littleEndian index))) store

private lemma decoded_execute (sample : CInputRef ctx (.bits (count * width)))
    (proposal : Fin count) (scratch : ScratchRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (TerminalDecode.intoFromBitRefs (model := model) .littleEndian
      (PackedSample.proposalRefs sample proposal) scratch.candidate).execute
        environment Reference state =
      state.mapClassical (fun entry =>
        let result := decodedStep (model := model) sample proposal scratch entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (TerminalDecode.terminalDecode_fold_execute scratch.candidate _ Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual decoded proposal and four-instruction suffix with their joint path. -/
def prefixStep (sample : CInputRef ctx (.bits (count * width))) (proposal : Fin count)
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width) (store : Store ctx) :
    Store ctx × (prefixBody (model := model) sample proposal shared scratch).Path :=
  let decoded := decodedStep (model := model) sample proposal scratch store
  let compared := comparisonStep (model := model) shared scratch decoded.1
  (compared.1, (decoded.2, compared.2))

/-- Prefix execution follows the actual decoder and comparison updates on every block. -/
lemma proposalPrefix_execute (sample : CInputRef ctx (.bits (count * width)))
    (proposal : Fin count) (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (prefixBody (model := model) sample proposal shared scratch).execute
      environment Reference state =
      state.mapClassical (fun entry =>
        let result := prefixStep (model := model) sample proposal shared scratch entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    _ (comparisonBody (model := model) shared scratch)
    (fun entry =>
      let result := decodedStep (model := model) sample proposal scratch entry.1
      ((result.1, entry.2), result.2))
    (fun entry =>
      let result := comparisonStep (model := model) shared scratch entry.1
      ((result.1, entry.2), result.2))
    (decoded_execute sample proposal scratch)
    (fun reference {_} _ initial => by
      refine (proposalComparison_execute shared scratch reference initial).trans ?_
      exact ExecutionState.executionState_mapClassical_congr _ rfl) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The true proposal-slot store and path, including the selector's stored branch. -/
def slotStep (sample : CInputRef ctx (.bits (count * width))) (proposal : Fin count)
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width) (store : Store ctx) :
    Store ctx × (slot (model := model) sample proposal shared scratch).Path :=
  let prefixed := prefixStep (model := model) sample proposal shared scratch store
  let selected := FirstAccepted.step (model := model) (selectorInputs scratch) shared.selector
    prefixed.1
  (selected.1, (prefixed.2, selected.2))

/-- One real slot composes the exact prefix and first-accepted state equations. -/
lemma proposalSlot_execute (sample : CInputRef ctx (.bits (count * width)))
    (proposal : Fin count) (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (slot (model := model) sample proposal shared scratch).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := slotStep (model := model) sample proposal shared scratch entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (prefixBody (model := model) sample proposal shared scratch) _
    (fun entry =>
      let result := prefixStep (model := model) sample proposal shared scratch entry.1
      ((result.1, entry.2), result.2))
    (fun entry =>
      let result := FirstAccepted.step (model := model) (selectorInputs scratch) shared.selector
        entry.1
      ((result.1, entry.2), result.2))
    (proposalPrefix_execute sample proposal shared scratch)
    (FirstAccepted.firstAccepted_execute (selectorInputs scratch) shared.selector)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Store and real nested path of the ordered finite proposal fold. -/
def foldSteps (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width) :
    (proposals : List (Fin count)) → Store ctx →
      Store ctx × (foldSlots (model := model) sample shared scratch proposals).Path
  | [], store => (store, ())
  | proposal :: remaining, store =>
      let selected := slotStep (model := model) sample proposal shared scratch store
      let later := foldSteps sample shared scratch remaining selected.1
      (later.1, (selected.2, later.2))

/-- Every finite ordered scan has the exact state map of its actual source-addressed slots. -/
lemma proposalFold_execute (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (proposals : List (Fin count)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (foldSlots (model := model) sample shared scratch proposals).execute
      environment Reference state =
      state.mapClassical (fun entry =>
        let result := foldSteps (model := model) sample shared scratch proposals entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  induction proposals generalizing Reference History with
  | nil =>
      refine (Circuit.execute_id_mapClassical (environment := environment) Reference state).trans ?_
      exact ExecutionState.executionState_mapClassical_congr _ rfl
  | cons proposal remaining ih =>
      refine (Circuit.execute_seq_mapClassical (environment := environment)
        (slot (model := model) sample proposal shared scratch)
        (foldSlots (model := model) sample shared scratch remaining)
        (fun entry =>
          let result := slotStep (model := model) sample proposal shared scratch entry.1
          ((result.1, entry.2), result.2))
        (fun entry =>
          let result := foldSteps (model := model) sample shared scratch remaining entry.1
          ((result.1, entry.2), result.2))
        (proposalSlot_execute sample proposal shared scratch)
        (fun reference {_} _ initial => ih reference initial) Reference state).trans ?_
      exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal
