/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Layout
import all QuantumAlg.Core.Execution.Classical.Iteration

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

private theorem initializeMapClassical_decision {C D : Type} [Fintype C] [Fintype D]
    {R : Register} (first second : DecidableEq D) (state : ExecutionState C R)
    (update : C → D) :
    @ExecutionState.mapClassical C D _ _ R first state update =
      @ExecutionState.mapClassical C D _ _ R second state update := by
  cases Subsingleton.elim first second
  rfl

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

/-- One actual in-place left shift of the binary-search half interval. -/
def shiftHalfInto (refs : Refs ctx inputWidth) : Circuit ctx ctx :=
  .classical (shiftHalfOp refs)

/-- A fixed number of actual native half-interval shifts. -/
def shiftHalfLoopInto (refs : Refs ctx inputWidth) (count : Nat) : Circuit ctx ctx :=
  .iterate count (shiftHalfInto refs)

/-- Actual final store and one native path for each shift in the loop. -/
def shiftHalfLoopStep (refs : Refs ctx inputWidth) (count : Nat) (store : Store ctx) :
    Store ctx × (shiftHalfLoopInto refs count).Path :=
  ((fun before => before.applyOp (shiftHalfOp refs))^[count] store, fun _ => ())

/-- The loop record follows the existing iterator on the full classical-quantum state. -/
theorem shiftHalfLoopInto_execute (refs : Refs ctx inputWidth) (count : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (shiftHalfLoopInto refs count).execute Reference state = state.mapClassical (fun entry =>
      ((shiftHalfLoopStep refs count entry.1).1,
        (entry.2, (shiftHalfLoopStep refs count entry.1).2))) := by
  refine (Circuit.execute_iterate_mapClassical (shiftHalfInto refs)
    (fun before => (before.applyOp (shiftHalfOp refs), ())) ?_ count Reference state).trans ?_
  · intro reference history _ before
    refine (Circuit.execute_classical_mapClassical (shiftHalfOp refs) reference before).trans ?_
    congr 1
    exact Subsingleton.elim _ _
  · dsimp only [shiftHalfLoopStep]
    exact initializeMapClassical_decision _ _ state _

/-- The original four initialization instructions followed by the required native shifts. -/
def initializeInto (refs : Refs ctx inputWidth) : Circuit ctx ctx :=
  .seq (.classical (initializeResizeOp refs))
    (.seq (.classical (initializeClearOp refs.round.root))
      (.seq (.classical (initializeClearOp refs.round.half))
        (.seq (.classical (initializeIncrementOp refs))
          (shiftHalfLoopInto refs (inputWidth - 1)))))

/-- The actual store after widening, clearing both interval cells and incrementing half. -/
def initializeSeed (refs : Refs ctx inputWidth) (store : Store ctx) : Store ctx :=
  (((store.applyOp (initializeResizeOp refs)).applyOp
    (initializeClearOp refs.round.root)).applyOp
      (initializeClearOp refs.round.half)).applyOp (initializeIncrementOp refs)

/-- Complete chronological store and path record of the actual initialization prefix. -/
def initializeStep (refs : Refs ctx inputWidth) (store : Store ctx) :
    Store ctx × (initializeInto refs).Path :=
  let shifted := shiftHalfLoopStep refs (inputWidth - 1) (initializeSeed refs store)
  (shifted.1, ((), ((), ((), ((), shifted.2)))))

/-- Initialization executes its exact record while retaining every incoming reference block. -/
theorem initializeInto_execute (refs : Refs ctx inputWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (initializeInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((initializeStep refs entry.1).1, (entry.2, (initializeStep refs entry.1).2))) := by
  simp only [initializeInto, initializeStep, initializeSeed, Circuit.execute_seq,
    Circuit.execute_classical_mapClassical, shiftHalfLoopInto_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt
