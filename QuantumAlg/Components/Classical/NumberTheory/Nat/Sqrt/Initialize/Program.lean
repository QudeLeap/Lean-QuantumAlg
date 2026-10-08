/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Layout
import all QuantumAlg.Core.Execution.Classical.Iteration
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Actual initialization of the binary square-root search

The native resize, two charged self-XOR clears, increment and fixed shift loop
overwrite arbitrary incoming workspace values on the complete caller store.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt

open Execution
open IntegerSqrt (writeInput)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {inputWidth : Nat}

/-- Native widening of the original input into the refinement input cell. -/
def initializeResizeOp (refs : Refs ctx inputWidth) :=
  ClassicalOp.wordResize inputWidth (workWidth inputWidth + workWidth inputWidth) ctx
    refs.input refs.wideInput

/-- Charged self-XOR clears an arbitrary word in place. -/
def initializeClearOp (output : CWriteRef ctx (.unsignedWord (workWidth inputWidth))) :=
  ClassicalOp.wordBinary .bitXor (workWidth inputWidth) ctx
    (.product (writeInput output) (writeInput output)) output

/-- Native increment of the newly cleared half interval. -/
def initializeIncrementOp (refs : Refs ctx inputWidth) :=
  ClassicalOp.wordUnary .increment (workWidth inputWidth) ctx
    (writeInput refs.round.half) refs.round.half

/-- Native in-place left shift of the half interval. -/
def shiftHalfOp (refs : Refs ctx inputWidth) :=
  ClassicalOp.wordUnary .shiftLeft (workWidth inputWidth) ctx
    (writeInput refs.round.half) refs.round.half

/-- The actual store after widening, clearing both interval cells and incrementing half. -/
def initializeSeed (refs : Refs ctx inputWidth) (store : Store ctx) : Store ctx :=
  (((store.applyOp (initializeResizeOp refs)).applyOp
    (initializeClearOp refs.round.root)).applyOp
      (initializeClearOp refs.round.half)).applyOp (initializeIncrementOp refs)

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- One actual in-place left shift of the binary-search half interval. -/
def shiftHalfInto (refs : Refs ctx inputWidth) : Circuit model ctx ctx :=
  BitWord.instruction (execution := model) (shiftHalfOp refs)

/-- A fixed number of actual native half-interval shifts. -/
def shiftHalfLoopInto (refs : Refs ctx inputWidth) (count : Nat) : Circuit model ctx ctx :=
  .iterate count (shiftHalfInto (model := model) refs)

/-- Actual final store and one native path for each shift in the loop. -/
def shiftHalfLoopStep (refs : Refs ctx inputWidth) (count : Nat) (store : Store ctx) :
    Store ctx × (shiftHalfLoopInto (model := model) refs count).Path :=
  ((fun before => before.applyOp (shiftHalfOp refs))^[count] store,
    fun index => (BitWord.instructionStep (execution := model) (shiftHalfOp refs)
      ((fun before => before.applyOp (shiftHalfOp refs))^[index.val] store)).2)

/-- The loop record follows the existing iterator on the full classical-quantum state. -/
theorem shiftHalfLoopInto_execute (refs : Refs ctx inputWidth) (count : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (shiftHalfLoopInto (model := model) refs count).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := shiftHalfLoopStep (model := model) refs count entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  let nativeStep := BitWord.instructionStep (execution := model) (shiftHalfOp refs)
  let jointStep := fun before : Store ctx × model.HiddenState =>
    let actual := nativeStep before.1
    ((actual.1, before.2), actual.2)
  have iterated (count : Nat) (store : Store ctx) (hidden : model.HiddenState) :
      ((fun before => (jointStep before).1)^[count]) (store, hidden) =
        (((fun before => (nativeStep before).1)^[count]) store, hidden) := by
    induction count generalizing store with
    | zero => rfl
    | succ count ih =>
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        exact ih (nativeStep store).1
  refine (Circuit.execute_iterate_mapClassical (shiftHalfInto (model := model) refs) jointStep
    (fun _reference _history _ current =>
      BitWord.bitWord_instruction_execute (shiftHalfOp refs) current)
    count Reference state).trans ?_
  apply ExecutionState.executionState_mapClassical_congr
  funext entry
  simp only [iterated]
  rfl

/-- The original four initialization instructions followed by the required native shifts. -/
def initializeInto (refs : Refs ctx inputWidth) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (initializeResizeOp refs))
    (.seq (BitWord.instruction (execution := model) (initializeClearOp refs.round.root))
      (.seq (BitWord.instruction (execution := model) (initializeClearOp refs.round.half))
        (.seq (BitWord.instruction (execution := model) (initializeIncrementOp refs))
          (shiftHalfLoopInto (model := model) refs (inputWidth - 1)))))

/-- Complete chronological store and path record of the actual initialization prefix. -/
def initializeStep (refs : Refs ctx inputWidth) (store : Store ctx) :
    Store ctx × (initializeInto (model := model) refs).Path :=
  let resized := BitWord.instructionStep (execution := model) (initializeResizeOp refs) store
  let root := BitWord.instructionStep (execution := model)
    (initializeClearOp refs.round.root) resized.1
  let half := BitWord.instructionStep (execution := model)
    (initializeClearOp refs.round.half) root.1
  let incremented := BitWord.instructionStep (execution := model) (initializeIncrementOp refs)
    half.1
  let shifted := shiftHalfLoopStep (model := model) refs (inputWidth - 1) incremented.1
  (shifted.1, (resized.2, (root.2, (half.2, (incremented.2, shifted.2)))))

/-- Initialization executes its exact record while retaining every incoming reference block. -/
theorem initializeInto_execute (refs : Refs ctx inputWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (initializeInto (model := model) refs).execute Reference state = state.mapClassical (fun entry
      =>
      let actual := initializeStep (model := model) refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [initializeInto, initializeStep, Circuit.execute_seq,
    BitWord.bitWord_instruction_execute, shiftHalfLoopInto_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt
