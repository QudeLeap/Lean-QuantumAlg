/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sub.Layout
import all QuantumAlg.Core.Execution.Classical.Composition.Record
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Actual compare-and-select natural subtraction

The comparison writes a real bit. Reading that bit selects either a native
self-XOR clear or a native word subtraction, on the complete caller store.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatSub

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Native comparison of the original two word operands. -/
def compareOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .lessThan width ctx (.product refs.left refs.right) refs.lessThan

/-- Native self-XOR overwrites any incoming output word with zero. -/
def clearOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .bitXor width ctx
    (.product (writeInput refs.output) (writeInput refs.output)) refs.output

/-- Native word subtraction reads both operands before overwriting the output. -/
def subtractOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .sub width ctx (.product refs.left refs.right) refs.output

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Actual selected one-instruction body. -/
def arm (refs : Refs ctx width) : CShape.Value .bit → Circuit model ctx ctx
  | .bit false => BitWord.instruction (execution := model) (subtractOp refs)
  | .bit true => BitWord.instruction (execution := model) (clearOp refs)

/-- Store update and actual path for one selected instruction. -/
def armStep (refs : Refs ctx width) (flag : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (arm (model := model) refs flag).Path :=
  match flag with
  | .bit false => BitWord.instructionStep (execution := model) (subtractOp refs) store
  | .bit true => BitWord.instructionStep (execution := model) (clearOp refs) store

/-- Read the real comparison latch and execute its selected native instruction. -/
def selectedInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .branch (writeInput refs.lessThan) (arm (model := model) refs)

/-- The actual selected instruction record includes the stored comparison value. -/
def selectedStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (selectedInto (model := model) refs).Path :=
  let flag := store.read (writeInput refs.lessThan)
  let chosen := armStep (model := model) refs flag store
  (chosen.1, ⟨flag, chosen.2⟩)

/-- Actual comparison followed by the stored-flag selection. -/
def into (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (compareOp refs)) (selectedInto (model := model)
    refs)

/-- Complete actual store and chronological path record of saturating subtraction. -/
def step (refs : Refs ctx width) (store : Store ctx) : Store ctx × (into (model := model)
  refs).Path :=
  let compared := BitWord.instructionStep (execution := model) (compareOp refs) store
  let selected := selectedStep (model := model) refs compared.1
  (selected.1, (compared.2, selected.2))

/-- The selected instruction runs on the real store produced by comparison. -/
lemma step_store (refs : Refs ctx width) (store : Store ctx) :
    (step (model := model) refs store).1 = (selectedStep (model := model) refs (store.applyOp
      (compareOp refs))).1 := rfl

/-- The selected store is the actual charged clear or subtraction update. -/
lemma selectedStep_store (refs : Refs ctx width) (store : Store ctx) :
    (selectedStep (model := model) refs store).1 =
      if (store.read (writeInput refs.lessThan)).toBool then store.applyOp (clearOp refs)
      else store.applyOp (subtractOp refs) := by
  unfold selectedStep
  cases stored : store.read (writeInput refs.lessThan) with
  | bit flag => cases flag <;> rfl

private lemma arm_execute (refs : Refs ctx width) (flag : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (arm (model := model) refs flag).execute environment Reference state
      = state.mapClassical (fun entry =>
      let actual := armStep (model := model) refs flag entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  cases flag with
  | bit flag =>
    cases flag
    all_goals exact BitWord.bitWord_instruction_execute (environment := environment) _ state

/-- Actual flag selection preserves every incoming history and quantum-reference block. -/
lemma selectedInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (selectedInto (model := model) refs).execute environment Reference state
      = state.mapClassical (fun entry =>
      let actual := selectedStep (model := model) refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_branch_mapClassical
    (environment := environment) (writeInput refs.lessThan) (arm (model := model) refs)
    (fun flag before =>
      let actual := armStep (model := model) refs flag before.1
      ((actual.1, before.2), actual.2))
    (fun flag reference _history _ current => arm_execute refs flag reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual circuit executes its exact record on the full incoming classical-quantum state. -/
lemma into_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) refs).execute environment Reference state
      = state.mapClassical (fun entry =>
      let actual := step (model := model) refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [into, step, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    selectedInto_execute, State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSub
