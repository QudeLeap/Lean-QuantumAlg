/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sub.Circuit

/-!
# Complete execution of the native saturating subtraction

The deterministic update below follows the actual comparison, selected word
instruction and matching lexical release. Its history is the real circuit
path, including the stored decision. The execution equation retains every
incoming quantum-reference block and all correlations with the original store.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSub

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Each selected native instruction returns its actual store and returned instruction path. -/
def selectedStep (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    (value : CShape.Value .bit) → Store (context ctx) →
      Store (context ctx) × (selected (model := model) left right output value).Path
  | .bit true, store => BitWord.instructionStep (execution := model) (clearOp output) store
  | .bit false, store => BitWord.instructionStep (execution := model) (subtractOp left right
    output) store

/-- The actual branch records the same comparison value that it reads. -/
def branchStep (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (context ctx)) :
    Store (context ctx) ×
      (Circuit.branch (.storage (decision ctx).toCStorageRef) (selected (model := model) left
        right output)).Path :=
  let value := store.read (.storage (decision ctx).toCStorageRef)
  let result := selectedStep (model := model) left right output value store
  (result.1, ⟨value, result.2⟩)

private lemma selected_equation (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx) Reference (model.HiddenState × History)) :
    (selected (model := model) left right output value).execute environment Reference state =
      state.mapClassical (fun entry =>
        ((selectedStep (model := model) left right output value entry.1).1,
          (entry.2.1, (entry.2.2, (selectedStep (model := model) left right output value
            entry.1).2)))) := by
  cases value with
  | bit flag => cases flag <;> exact BitWord.bitWord_instruction_execute _ environment state

private lemma branch_equation (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State (context ctx) Reference (model.HiddenState ×
      History)) :
    (Circuit.branch (.storage (decision ctx).toCStorageRef)
      (selected (model := model) left right output)).execute environment Reference state =
        state.mapClassical (fun entry =>
          ((branchStep (model := model) left right output entry.1).1,
            (entry.2.1, (entry.2.2, (branchStep (model := model) left right output entry.1).2))))
              := by
  refine (Circuit.execute_branch_mapClassical (environment := environment)
    (.storage (decision ctx).toCStorageRef) (selected (model := model) left right output)
    (fun flag before =>
      let actual := selectedStep (model := model) left right output flag before.1
      ((actual.1, before.2), actual.2))
    (fun flag reference _history _ current => selected_equation left right output flag reference
      current) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The body performs its real comparison before the selected output instruction. -/
def bodyStep (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (context ctx)) :
    Store (context ctx) × (body (model := model) left right output).Path :=
  let compared := BitWord.instructionStep (execution := model) (compareOp left right) store
  let result := branchStep (model := model) left right output compared.1
  (result.1, (compared.2, result.2))

/-- The actual body preserves the full incoming quantum-reference state in every classical block. -/
lemma nativeSub_body_execute (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State (context ctx) Reference (model.HiddenState ×
      History)) :
    (body (model := model) left right output).execute environment
      Reference state = state.mapClassical (fun
      entry =>
      ((bodyStep (model := model) left right output entry.1).1,
        (entry.2.1, (entry.2.2, (bodyStep (model := model) left right output entry.1).2)))) := by
  simp only [body, bodyStep, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    branch_equation, State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual lexical entry, body execution and release of the one decision cell. -/
def intoStep (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (into (model := model) left right output).Path :=
  let entered := store.pushWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
  let result := bodyStep (model := model) left right output entered
  (Store.popWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh result.1, result.2)

/-- Every actual execution agrees with the complete store update and its genuine finite path. -/
lemma nativeSub_into_execute (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) left right output).execute environment
      Reference state = state.mapClassical (fun
      entry =>
      ((intoStep (model := model) left right output entry.1).1,
        (entry.2.1, (entry.2.2, (intoStep (model := model) left right output entry.1).2)))) := by
  refine (Circuit.execute_workspace_mapClassical
    (environment := environment) ctx.canonicalFreshKey .bit
    ctx.canonicalFreshKey_fresh (body (model := model) left right output)
    (fun before =>
      let actual := bodyStep (model := model) left right output before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => nativeSub_body_execute left right output reference current)
    Reference state).trans ?_
  congr 1

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSub
