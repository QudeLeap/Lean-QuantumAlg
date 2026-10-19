/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.IntegerSqrt.Layout
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Actual binary integer-square-root refinement round
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.IntegerSqrt

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Carrying addition that constructs the candidate midpoint. -/
def addOp {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) :=
  ClassicalOp.addCarry width ctx
    (.product (writeInput refs.root) (writeInput refs.half)) refs.midCarry

/-- Full-width square of the candidate midpoint. -/
def squareOp {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) :=
  ClassicalOp.mulFull width width ctx
    (.product (.first (writeInput refs.midCarry)) (.first (writeInput refs.midCarry))) refs.square

/-- Comparison of the input with the squared candidate midpoint. -/
def compareOp {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : Refs ctx width) :=
  ClassicalOp.wordBinary .lessThan (width + width) ctx
    (.product input (writeInput refs.square)) refs.tooLarge

/-- Negation of the too-large flag used as the candidate-selection bit. -/
def takeOp {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat} (refs : Refs ctx width) :=
  ClassicalOp.bit .not ctx (writeInput refs.tooLarge) refs.take

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The selected root copy uses the midpoint or the original root according to the stored flag. -/
def rootOp (refs : Refs ctx width) (take : Bool) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx
    (if take then .first (writeInput refs.midCarry) else writeInput refs.root) refs.root

/-- The original half increment is divided by two with one native right shift. -/
def halfOp (refs : Refs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .shiftRight width ctx (writeInput refs.half) refs.half

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Four native writes compute the candidate midpoint, square, comparison and selection flag. -/
def roundPrefixInto (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (addOp refs))
    (.seq (BitWord.instruction (execution := model) (squareOp refs))
      (.seq (BitWord.instruction (execution := model) (compareOp input refs)) (BitWord.instruction
        (execution := model) (takeOp refs))))

/-- The chronological actual prefix store and its four native instruction paths. -/
def roundPrefixStep (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (store : Store ctx) : Store ctx × (roundPrefixInto (model := model)
      input refs).Path :=
  let added := BitWord.instructionStep (execution := model) (addOp refs) store
  let squared := BitWord.instructionStep (execution := model) (squareOp refs) added.1
  let compared := BitWord.instructionStep (execution := model) (compareOp input refs) squared.1
  let taken := BitWord.instructionStep (execution := model) (takeOp refs) compared.1
  (taken.1, (added.2, (squared.2, (compared.2, taken.2))))

/-- The four original writes preserve every history and the full quantum-reference state. -/
lemma roundPrefixInto_execute (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (roundPrefixInto (model := model) input refs).execute environment Reference state
      = state.mapClassical
      (fun entry =>
      let actual := roundPrefixStep (model := model) input refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [roundPrefixInto, roundPrefixStep, Circuit.execute_seq,
    BitWord.bitWord_instruction_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual take-cell read dispatches the original root-copy instruction. -/
def rootInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .branch (writeInput refs.take) fun value => BitWord.instruction (execution := model) (rootOp
    refs value.toBool)

/-- The root store and recorded flag come from the same actual incoming state. -/
def rootStep (refs : Refs ctx width) (store : Store ctx) : Store ctx × (rootInto (model := model)
  refs).Path :=
  let flag := store.read (writeInput refs.take)
  let actual := BitWord.instructionStep (execution := model) (rootOp refs flag.toBool) store
  (actual.1, ⟨flag, actual.2⟩)

/-- The actual stored flag selects the executed copy and is retained in its path. -/
lemma rootInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (rootInto (model := model) refs).execute environment Reference state
      = state.mapClassical (fun entry =>
      let actual := rootStep (model := model) refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_branch_mapClassical (environment := environment) (writeInput refs.take)
    (fun value => BitWord.instruction (execution := model) (rootOp refs value.toBool))
    (fun value before =>
      let actual := BitWord.instructionStep (execution := model) (rootOp refs value.toBool) before.1
      ((actual.1, before.2), actual.2))
    (fun value _reference _history _ current =>
      BitWord.bitWord_instruction_execute
        (environment := environment) (rootOp refs value.toBool) current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The original four-write prefix, stored-flag root copy and native half shift. -/
def roundInto (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (roundPrefixInto (model := model) input refs) (.seq (rootInto (model := model) refs)
    (BitWord.instruction (execution := model) (halfOp refs)))

/-- Complete actual final store and chronological path of the original refinement round. -/
def roundStep (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (store : Store ctx) : Store ctx × (roundInto (model := model) input
      refs).Path :=
  let prefixResult := roundPrefixStep (model := model) input refs store
  let root := rootStep (model := model) refs prefixResult.1
  let shifted := BitWord.instructionStep (execution := model) (halfOp refs) root.1
  (shifted.1, (prefixResult.2, (root.2, shifted.2)))

/-- Complete real execution retains prior histories and all original quantum-reference blocks. -/
lemma roundInto_execute (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (roundInto (model := model) input refs).execute environment Reference state
      = state.mapClassical (fun
      entry =>
      let actual := roundStep (model := model) input refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [roundInto, roundStep, Circuit.execute_seq, roundPrefixInto_execute,
    rootInto_execute, BitWord.bitWord_instruction_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.IntegerSqrt
