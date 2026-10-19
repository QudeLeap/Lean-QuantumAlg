/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Model.BitWord.Iteration
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Actual unsigned word splitting

A low-width resize reads the original working word. Native one-bit right
shifts then remove the low part, and a high-width resize writes the remaining
high part. All operations execute in the single actual circuit interpreter.
-/

namespace QuantumAlg.ClassicalRoutines.Word.Split

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Caller-owned working word and the two separately addressed output words. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (highWidth lowWidth : Nat) where
  work : CWriteRef ctx (.unsignedWord (highWidth + lowWidth))
  high : CWriteRef ctx (.unsignedWord highWidth)
  low : CWriteRef ctx (.unsignedWord lowWidth)

/-- Exactly the three original write identities must be distinct. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {highWidth lowWidth : Nat}
    (refs : Refs ctx highWidth lowWidth) : Prop where
  workNeLow : refs.work.key ≠ refs.low.key
  workNeHigh : refs.work.key ≠ refs.high.key
  highNeLow : refs.high.key ≠ refs.low.key

section Descriptor

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width highWidth lowWidth : Nat}

/-- One actual unsigned division by two, encoded as the native right-shift instruction. -/
def shiftOp (work : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .shiftRight width ctx (.storage work.toCStorageRef) work

/-- The chronological actual store of the fixed number of native shifts. -/
def shiftStore (count : Nat) (work : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx :=
  (fun current => current.applyOp (shiftOp work))^[count] store

/-- Resize the original working word to its low-width remainder. -/
def lowOp (refs : Refs ctx highWidth lowWidth) :
    ClassicalOp (.unsignedWord (highWidth + lowWidth)) (.unsignedWord lowWidth) ctx ctx :=
  .wordResize (highWidth + lowWidth) lowWidth ctx (.storage refs.work.toCStorageRef) refs.low

/-- Resize the shifted working word to its high-width output. -/
def highOp (refs : Refs ctx highWidth lowWidth) :
    ClassicalOp (.unsignedWord (highWidth + lowWidth)) (.unsignedWord highWidth) ctx ctx :=
  .wordResize (highWidth + lowWidth) highWidth ctx (.storage refs.work.toCStorageRef) refs.high

end Descriptor

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width highWidth lowWidth : Nat}

/-- Perform the prescribed number of native shifts on the actual working word. -/
def shiftInto (count : Nat) (work : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  BitWord.repeatInstruction (execution := model) (shiftOp work) count

/-- Actual shift store together with every chronological native output. -/
def shiftStep (count : Nat) (work : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (shiftInto (model := model) count work).Path :=
  BitWord.repeatStep (execution := model) (shiftOp work) count store

/-- The actual shifts retain shared service state and every original quantum-reference block. -/
lemma shiftInto_execute (count : Nat) (work : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (shiftInto (model := model) count work).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := shiftStep (model := model) count work entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  BitWord.bitWord_repeatInstruction_execute (execution := model) (shiftOp work) count state

/-- The actual shift iteration feeds the final high-width resize. -/
def tailInto (refs : Refs ctx highWidth lowWidth) : Circuit model ctx ctx :=
  .seq (shiftInto (model := model) lowWidth refs.work)
    (BitWord.instruction (execution := model) (highOp refs))

/-- Actual shifted and high-output store with its chronological native path. -/
def tailStep (refs : Refs ctx highWidth lowWidth) (store : Store ctx) :
    Store ctx × (tailInto (model := model) refs).Path :=
  let first := shiftStep (model := model) lowWidth refs.work store
  let last := BitWord.instructionStep (execution := model) (highOp refs) first.1
  (last.1, (first.2, last.2))

/-- Actual shifts and the final output write compose on the complete state and service record. -/
lemma tailInto_execute (refs : Refs ctx highWidth lowWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (tailInto (model := model) refs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := tailStep (model := model) refs entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (shiftInto (model := model) lowWidth refs.work)
    (BitWord.instruction (execution := model) (highOp refs))
    (fun before =>
      let result := shiftStep (model := model) lowWidth refs.work before.1
      ((result.1, before.2), result.2))
    (fun before =>
      let result := BitWord.instructionStep (execution := model) (highOp refs) before.1
      ((result.1, before.2), result.2)) ?_ ?_ Reference state).trans ?_
  · intro reference history _ state
    exact (shiftInto_execute (model := model) lowWidth refs.work reference state).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history _ state
    exact (BitWord.bitWord_instruction_execute
      (environment := environment) (execution := model) (highOp refs) state).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Split by the original low resize, repeated one-bit shift and high resize sequence. -/
def splitInto (refs : Refs ctx highWidth lowWidth) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (lowOp refs)) (tailInto (model := model) refs)

/-- Complete actual final store and chronological path of the word split. -/
def splitStep (refs : Refs ctx highWidth lowWidth) (store : Store ctx) :
    Store ctx × (splitInto (model := model) refs).Path :=
  let first := BitWord.instructionStep (execution := model) (lowOp refs) store
  let tail := tailStep (model := model) refs first.1
  (tail.1, (first.2, tail.2))

/-- Actual low extraction, shifts and high extraction preserve all original state correlations. -/
lemma splitInto_execute (refs : Refs ctx highWidth lowWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (splitInto (model := model) refs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := splitStep (model := model) refs entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (BitWord.instruction (execution := model) (lowOp refs)) (tailInto (model := model) refs)
    (fun before =>
      let result := BitWord.instructionStep (execution := model) (lowOp refs) before.1
      ((result.1, before.2), result.2))
    (fun before =>
      let result := tailStep (model := model) refs before.1
      ((result.1, before.2), result.2)) ?_ ?_ Reference state).trans ?_
  · intro reference history _ state
    exact (BitWord.bitWord_instruction_execute
      (environment := environment) (execution := model) (lowOp refs) state).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history _ state
    exact (tailInto_execute (model := model) refs reference state).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.ClassicalRoutines.Word.Split
