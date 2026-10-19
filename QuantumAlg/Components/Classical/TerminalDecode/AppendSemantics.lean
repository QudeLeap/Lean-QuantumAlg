/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.TerminalDecode.Circuit
import all QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Exact state update of one terminal-bit append

The intermediate bit is read from the store produced by the real shift.
The full-state equation therefore holds even if a caller aliases that read
with the output word. The ordinary nonaliasing wire arrangement additionally
identifies this read with the original source bit. Each theorem preserves the
entire quantum-reference block; only the named classical word is written.
-/

namespace QuantumAlg.ClassicalRoutines.TerminalDecode

open Execution
open ClassicalAlgorithms.TerminalDecode

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def incrementChoiceStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}
    (output : CWriteRef ctx (OutputShape width)) (value : CShape.Value .bit)
    (store : Store ctx) : Store ctx ×
      (if value.toBool then BitWord.instruction (execution := model) (incrementOp width output)
        else Circuit.id (model := model) ctx).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => BitWord.instructionStep (execution := model) (incrementOp width output) store

private lemma incrementChoice_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat} (output : CWriteRef ctx (OutputShape width))
    (value : CShape.Value .bit) {environment : model.Environment}
    (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (if value.toBool then BitWord.instruction (execution := model) (incrementOp width output)
      else Circuit.id (model := model) ctx).execute environment Reference state =
        state.mapClassical (fun entry =>
          let result := incrementChoiceStep (model := model) output value entry.1
          (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  cases value with
  | bit bit =>
      cases bit
      · simp only [CShape.Value.toBool, incrementChoiceStep]
        exact (Circuit.execute_id_mapClassical (environment := environment) Reference state).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)
      · simp only [CShape.Value.toBool, incrementChoiceStep]
        exact BitWord.bitWord_instruction_execute (environment := environment) (execution := model)
          (incrementOp width output) state

/-- The concrete store and path obtained by shifting and reading its actual selected bit. -/
def appendStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}
    (input : CInputRef ctx .bit) (output : CWriteRef ctx (OutputShape width))
    (store : Store ctx) : Store ctx × (bitRefRoutine (model := model) input output).Path :=
  let shifted := BitWord.instructionStep (execution := model) (shiftOp width output) store
  let choice := shifted.1.read input
  let selected := incrementChoiceStep (model := model) output choice shifted.1
  (selected.1, (shifted.2, ⟨choice, selected.2⟩))

private lemma appendStep_store {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}
    (input : CInputRef ctx .bit) (output : CWriteRef ctx (OutputShape width))
    (store : Store ctx) :
    (appendStep (model := model) input output store).1 =
      if ((store.applyOp (shiftOp width output)).read input).toBool then
        (store.applyOp (shiftOp width output)).applyOp (incrementOp width output)
      else store.applyOp (shiftOp width output) := by
  change (incrementChoiceStep (model := model) output
    ((store.applyOp (shiftOp width output)).read input)
    (store.applyOp (shiftOp width output))).1 = _
  cases choice : (store.applyOp (shiftOp width output)).read input with
  | bit bit => cases bit <;> rfl

/-- The actual append preserves the complete service/reference state and chosen native path. -/
lemma terminalDecode_append_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat} (input : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) {environment : model.Environment}
    (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (bitRefRoutine (model := model) input output).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := appendStep (model := model) input output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (BitWord.instruction (execution := model) (shiftOp width output))
    (.branch input (fun value =>
      if value.toBool then BitWord.instruction (execution := model) (incrementOp width output)
        else .id ctx))
    (fun before =>
      let result := BitWord.instructionStep (execution := model) (shiftOp width output) before.1
      ((result.1, before.2), result.2))
    (fun before =>
      let choice := before.1.read input
      let result := incrementChoiceStep (model := model) output choice before.1
      ((result.1, before.2), ⟨choice, result.2⟩)) ?_ ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (BitWord.bitWord_instruction_execute
      (environment := environment) (execution := model) (shiftOp width output)
      initial).trans (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history _ initial
    refine (Circuit.execute_branch_mapClassical (environment := environment) input _
      (fun value before =>
        let result := incrementChoiceStep (model := model) output value before.1
        ((result.1, before.2), result.2)) ?_ reference initial).trans ?_
    · intro value reference history _ initial
      exact (incrementChoice_execute (model := model) output value reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
    · exact ExecutionState.executionState_mapClassical_congr _ rfl
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The exact overwritten word implements wrapping shift-and-append on its original source bit. -/
lemma terminalDecode_append_read_output {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    {width : Nat} (input : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) (store : Store ctx)
    (separate : output.key ∉ input.storageKeys) :
    ((appendStep (model := model) input output store).1.read (writeInput output)).toNat =
      appendBit (store.read (writeInput output)).toNat (store.read input).toBool %
        CShape.wordModulus width := by
  have frame : (store.applyOp (shiftOp width output)).read input = store.read input :=
    Store.read_applyOp_of_not_mem_storageKeys store (shiftOp width output) input separate
  have shifted := Store.read_applyOp_output store (shiftOp width output)
  change (store.applyOp (shiftOp width output)).read (writeInput output) =
    CShape.wordShiftLeft width (store.read (writeInput output)) at shifted
  rw [appendStep_store, frame]
  cases sampled : store.read input with
  | bit bit =>
      cases bit
      · simpa only [appendBit, CShape.Value.toBool, Bool.false_eq_true, if_false,
          Bool.toNat_false, Nat.add_zero,
          CShape.wordShiftLeft, CShape.wordOfNat_val] using
          congrArg CShape.Value.toNat shifted
      · have incremented := Store.read_applyOp_output
          (store.applyOp (shiftOp width output)) (incrementOp width output)
        change ((store.applyOp (shiftOp width output)).applyOp
          (incrementOp width output)).read (writeInput output) =
            CShape.wordOfNat width
              (((store.applyOp (shiftOp width output)).read (writeInput output)).toNat + 1)
          at incremented
        rw [shifted] at incremented
        simpa only [appendBit, CShape.Value.toBool, if_true, Bool.toNat_true,
          CShape.wordShiftLeft, CShape.wordOfNat_val, Nat.add_mod, Nat.mod_mod] using
          congrArg CShape.Value.toNat incremented

/-- The same exact append preserves every structural read outside its only written word. -/
lemma terminalDecode_append_read_other {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    {width : Nat} {observed : CShape} (input : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) (store : Store ctx)
    (other : CInputRef ctx observed)
    (separate : output.key ∉ other.storageKeys) :
    (appendStep (model := model) input output store).1.read other = store.read other := by
  have shifted : (store.applyOp (shiftOp width output)).read other = store.read other :=
    Store.read_applyOp_of_not_mem_storageKeys store (shiftOp width output) other separate
  rw [appendStep_store]
  split
  · exact (Store.read_applyOp_of_not_mem_storageKeys
      (store.applyOp (shiftOp width output)) (incrementOp width output) other separate).trans
      shifted
  · exact shifted

end

end QuantumAlg.ClassicalRoutines.TerminalDecode
