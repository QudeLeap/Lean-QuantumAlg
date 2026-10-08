/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Layout
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Actual stored-bit first-success control flow
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted.Direct

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Copy the actual eligible candidate into the persistent selected word. -/
def selectedOp (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx candidate refs.selected

/-- Copy the actual true eligibility bit into the persistent accepted latch. -/
def acceptedOp (eligible : CInputRef ctx .bit) (refs : Refs ctx width) :
    ClassicalOp .bit .bit ctx ctx := .bit .copy ctx eligible refs.accepted

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The actual candidate-eligibility arm either writes both persistent outputs or does nothing. -/
def eligibleArm (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width) :
    CShape.Value .bit → Circuit model ctx ctx
  | .bit false => .id ctx
  | .bit true => .seq (BitWord.instruction (execution := model) (selectedOp candidate refs))
      (BitWord.instruction (execution := model) (acceptedOp eligible refs))

/-- The chosen eligibility arm's actual chronological store updates and instruction paths. -/
def eligibleArmStep (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (eligibleArm (model := model) eligible candidate refs value).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true =>
      let first := BitWord.instructionStep (execution := model) (selectedOp candidate refs) store
      let second := BitWord.instructionStep (execution := model) (acceptedOp eligible refs) first.1
      (second.1, (first.2, second.2))

/-- Only a still-unaccepted result permits reading and acting on the actual candidate predicate. -/
def pendingArm (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width) :
    CShape.Value .bit → Circuit model ctx ctx
  | .bit false => .branch eligible (eligibleArm (model := model) eligible candidate refs)
  | .bit true => .id ctx

/-- The pending arm follows the real eligibility cell; an accepted result keeps its entire store. -/
def pendingArmStep (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (pendingArm (model := model) eligible candidate refs value).Path :=
  match value with
  | .bit false =>
      let chosen := eligibleArmStep (model := model) eligible candidate refs (store.read eligible)
        store
      (chosen.1, ⟨store.read eligible, chosen.2⟩)
  | .bit true => (store, ())

/-- Read the real accepted latch before deciding whether any candidate write is still allowed. -/
def into (eligible : CInputRef ctx .bit) (candidate : CInputRef ctx (.unsignedWord width))
    (refs : Refs ctx width) : Circuit model ctx ctx :=
  .branch (writeInput refs.accepted) (pendingArm (model := model) eligible candidate refs)

/-- The complete actual store result and both actually selected branch histories. -/
def step (eligible : CInputRef ctx .bit) (candidate : CInputRef ctx (.unsignedWord width))
    (refs : Refs ctx width) (store : Store ctx) : Store ctx × (into (model := model) eligible
      candidate refs).Path :=
  let chosen := pendingArmStep (model := model) eligible candidate refs (store.read (writeInput
    refs.accepted)) store
  (chosen.1, ⟨store.read (writeInput refs.accepted), chosen.2⟩)

/-- The actual eligibility arm preserves complete incoming quantum-reference blocks. -/
theorem eligibleArm_execute (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (eligibleArm (model := model) eligible candidate refs value).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := eligibleArmStep (model := model) eligible candidate refs value entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  cases value with
  | bit value =>
      cases value
      · exact (Circuit.execute_id_mapClassical Reference state).trans (by
          exact ExecutionState.executionState_mapClassical_congr _ rfl)
      · simp only [eligibleArm, eligibleArmStep, Circuit.execute_seq,
          BitWord.bitWord_instruction_execute, State.mapHistory,
          ExecutionState.executionState_mapClassical_comp, Function.comp_def]
        exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual pending selection reads the existing eligibility cell without computing a scratch
flag. -/
theorem pendingArm_execute (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pendingArm (model := model) eligible candidate refs value).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := pendingArmStep (model := model) eligible candidate refs value entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  cases value with
  | bit value =>
      cases value
      · refine (Circuit.execute_branch_mapClassical eligible
          (eligibleArm (model := model) eligible candidate refs)
          (fun value before =>
            let actual := eligibleArmStep (model := model) eligible candidate refs value before.1
            ((actual.1, before.2), actual.2))
          (fun value reference history _ state =>
            eligibleArm_execute eligible candidate refs value reference state)
          Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl
      · exact (Circuit.execute_id_mapClassical Reference state).trans (by
          exact ExecutionState.executionState_mapClassical_congr _ rfl)

/-- The full actual first-success interpreter uses precisely the two existing stored predicates. -/
theorem into_execute (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) eligible candidate refs).execute Reference state = state.mapClassical
      (fun entry =>
        let actual := step (model := model) eligible candidate refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_branch_mapClassical (writeInput refs.accepted)
    (pendingArm (model := model) eligible candidate refs)
    (fun value before =>
      let actual := pendingArmStep (model := model) eligible candidate refs value before.1
      ((actual.1, before.2), actual.2))
    (fun value reference history _ state =>
      pendingArm_execute eligible candidate refs value reference state)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.ClassicalRoutines.FirstAccepted.Direct
