/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Iteration
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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width highWidth lowWidth : Nat}

/-- One actual unsigned division by two, encoded as the native right-shift instruction. -/
def shiftOp (work : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .shiftRight width ctx (.storage work.toCStorageRef) work

/-- Perform the prescribed number of native shifts on the actual working word. -/
def shiftInto (count : Nat) (work : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .iterate count (.classical (shiftOp work))

/-- The chronological actual store of the fixed number of native shifts. -/
def shiftStore (count : Nat) (work : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx :=
  (fun current => current.applyOp (shiftOp work))^[count] store

/-- Actual shift store together with every native one-instruction path. -/
def shiftStep (count : Nat) (work : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (shiftInto count work).Path := (shiftStore count work store, fun _ => ())

set_option maxHeartbeats 800000 in
-- Normalize the finite iteration path and its constant atomic paths.
/-- The actual native shift iteration preserves all histories and quantum-reference blocks. -/
theorem shiftInto_execute (count : Nat) (work : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (shiftInto count work).execute Reference state = state.mapClassical (fun entry =>
      ((shiftStep count work entry.1).1, (entry.2, (shiftStep count work entry.1).2))) := by
  refine (Circuit.execute_iterate_mapClassical (.classical (shiftOp work))
    (fun store => (store.applyOp (shiftOp work), ()))
    (by
      intro Reference History _ state
      refine (Circuit.execute_classical_mapClassical (shiftOp work) Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) count Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Resize the original working word to its low-width remainder. -/
def lowOp (refs : Refs ctx highWidth lowWidth) :
    ClassicalOp (.unsignedWord (highWidth + lowWidth)) (.unsignedWord lowWidth) ctx ctx :=
  .wordResize (highWidth + lowWidth) lowWidth ctx (.storage refs.work.toCStorageRef) refs.low

/-- Resize the shifted working word to its high-width output. -/
def highOp (refs : Refs ctx highWidth lowWidth) :
    ClassicalOp (.unsignedWord (highWidth + lowWidth)) (.unsignedWord highWidth) ctx ctx :=
  .wordResize (highWidth + lowWidth) highWidth ctx (.storage refs.work.toCStorageRef) refs.high

/-- The actual shift iteration feeds the final high-width resize. -/
def tailInto (refs : Refs ctx highWidth lowWidth) : Circuit ctx ctx :=
  .seq (shiftInto lowWidth refs.work) (.classical (highOp refs))

/-- Actual shifted and high-output store with its chronological native path. -/
def tailStep (refs : Refs ctx highWidth lowWidth) (store : Store ctx) :
    Store ctx × (tailInto refs).Path :=
  ((shiftStore lowWidth refs.work store).applyOp (highOp refs), ((fun _ => ()), ()))

/-- Actual shifts and the final output write compose in the full execution state. -/
theorem tailInto_execute (refs : Refs ctx highWidth lowWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (tailInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((tailStep refs entry.1).1, (entry.2, (tailStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (shiftInto lowWidth refs.work) (.classical (highOp refs))
    (shiftStep lowWidth refs.work) (fun store => (store.applyOp (highOp refs), ()))
    (shiftInto_execute lowWidth refs.work) (by
      intro Reference History _ state
      refine (Circuit.execute_classical_mapClassical (highOp refs) Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Split by the original low resize, repeated one-bit shift and high resize sequence. -/
def splitInto (refs : Refs ctx highWidth lowWidth) : Circuit ctx ctx :=
  .seq (.classical (lowOp refs)) (tailInto refs)

/-- Complete actual final store and chronological path of the word split. -/
def splitStep (refs : Refs ctx highWidth lowWidth) (store : Store ctx) :
    Store ctx × (splitInto refs).Path :=
  let tail := tailStep refs (store.applyOp (lowOp refs))
  (tail.1, ((), tail.2))

/-- Actual low extraction, shifts and high extraction compose without losing state correlations. -/
theorem splitInto_execute (refs : Refs ctx highWidth lowWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (splitInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((splitStep refs entry.1).1, (entry.2, (splitStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (lowOp refs)) (tailInto refs)
    (fun store => (store.applyOp (lowOp refs), ())) (tailStep refs)
    (by
      intro Reference History _ state
      refine (Circuit.execute_classical_mapClassical (lowOp refs) Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) (tailInto_execute refs)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.ClassicalRoutines.Word.Split
