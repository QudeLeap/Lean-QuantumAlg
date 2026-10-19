/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.FirstAccepted.Circuit
public import QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Components.Classical.FirstAccepted.Circuit
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Exact block semantics of the native first-accepted selector

The real decision writes and stored branch determine one exact store and path
update. Its equality preserves every incoming quantum-reference matrix block,
including arbitrary correlations. Semantic separation of the selected latches
is proved separately; this execution equation holds for all supplied references.
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted

open Execution

noncomputable section

attribute [local instance] Classical.decEq

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The two real Boolean instructions update the full state without altering its quantum block. -/
public lemma firstAccepted_decision_execute (inputs : Inputs ctx width) (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (decisionBody (model := model) inputs refs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := decisionStep (model := model) inputs refs entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  simp only [decisionBody, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual selected arm copies the word and take latch with the exact two-instruction path. -/
public lemma firstAccepted_copy_execute (inputs : Inputs ctx width) (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (copyBody (model := model) inputs refs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := copyStep (model := model) inputs refs entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  simp only [copyBody, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Store update and dependent path selected by one actual take-bit value. -/
public def copyChoiceStep (inputs : Inputs ctx width) (refs : Refs ctx width)
    (value : CShape.Value .bit) (store : Store ctx) : Store ctx ×
      (if value.toBool then copyBody (model := model) inputs refs else Circuit.id (model := model)
        ctx).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => copyStep (model := model) inputs refs store

public lemma copyChoice_execute (inputs : Inputs ctx width) (refs : Refs ctx width)
    (value : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (if value.toBool then copyBody (model := model) inputs refs else Circuit.id (model := model)
      ctx).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := copyChoiceStep (model := model) inputs refs value entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  cases value with
  | bit bit =>
      cases bit
      · exact (Circuit.execute_id_mapClassical (environment := environment) Reference state).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)
      · exact (firstAccepted_copy_execute (model := model) inputs refs Reference state).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)


/-- The store and dependent path chosen by the actual take bit. -/
public def conditionalStep (inputs : Inputs ctx width) (refs : Refs ctx width)
    (store : Store ctx) : Store ctx × (conditionalCopy (model := model) inputs refs).Path :=
  let value := store.read (cellRead refs.take)
  let selected := copyChoiceStep (model := model) inputs refs value store
  (selected.1, ⟨value, selected.2⟩)

/-- The branch maps each input block through its own stored take value. -/
public lemma firstAccepted_conditional_execute (inputs : Inputs ctx width) (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (conditionalCopy (model := model) inputs refs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := conditionalStep (model := model) inputs refs entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_branch_mapClassical (environment := environment) (cellRead refs.take) _
    (fun value before =>
      let result := copyChoiceStep (model := model) inputs refs value before.1
      ((result.1, before.2), result.2))
    (fun value reference history _ state =>
      (copyChoice_execute (model := model) inputs refs value reference state).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)) Reference state).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)


/-- The concrete store and real nested path of the complete selector. -/
public def step (inputs : Inputs ctx width) (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (circuit (model := model) inputs refs).Path :=
  let decision := decisionStep (model := model) inputs refs store
  let selected := conditionalStep (model := model) inputs refs decision.1
  (selected.1, (decision.2, selected.2))

/-- The selector's complete state is the exact actual store map on every external reference. -/
public lemma firstAccepted_execute (inputs : Inputs ctx width) (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (circuit (model := model) inputs refs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := step (model := model) inputs refs entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (decisionBody (model := model) inputs refs) (conditionalCopy (model := model) inputs refs)
    (fun before =>
      let result := decisionStep (model := model) inputs refs before.1
      ((result.1, before.2), result.2))
    (fun before =>
      let result := conditionalStep (model := model) inputs refs before.1
      ((result.1, before.2), result.2))
    (fun reference history _ state =>
      (firstAccepted_decision_execute (model := model) inputs refs reference state).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl))
    (fun reference history _ state =>
      (firstAccepted_conditional_execute (model := model) inputs refs reference state).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)) Reference state).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)


/-- The complete store update is the real decision followed by its selected or empty copy arm. -/
public lemma firstAccepted_step_store (inputs : Inputs ctx width) (refs : Refs ctx width)
    (store : Store ctx) :
    (step (model := model) inputs refs store).1 =
      let decision := decisionStore inputs refs store
      if (decision.read (cellRead refs.take)).toBool then
        copyStore inputs refs decision else decision := by
  dsimp only [step, conditionalStep]
  change (copyChoiceStep (model := model) inputs refs
    ((decisionStore inputs refs store).read (cellRead refs.take))
    (decisionStore inputs refs store)).1 = _
  cases value : (decisionStore inputs refs store).read (cellRead refs.take) with
  | bit bit => cases bit <;> rfl

end

end QuantumAlg.ClassicalRoutines.FirstAccepted
