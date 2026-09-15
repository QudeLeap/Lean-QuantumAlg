/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sub.Layout
import all QuantumAlg.Core.Execution.Classical.Composition.Record

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

/-- Actual selected one-instruction body. -/
def arm (refs : Refs ctx width) : CShape.Value .bit → Circuit ctx ctx
  | .bit false => .classical (subtractOp refs)
  | .bit true => .classical (clearOp refs)

/-- Store update and actual path for one selected instruction. -/
def armStep (refs : Refs ctx width) (flag : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (arm refs flag).Path :=
  match flag with
  | .bit false => (store.applyOp (subtractOp refs), ())
  | .bit true => (store.applyOp (clearOp refs), ())

/-- Read the real comparison latch and execute its selected native instruction. -/
def selectedInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .branch (writeInput refs.lessThan) (arm refs)

/-- The actual selected instruction record includes the stored comparison value. -/
def selectedStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (selectedInto refs).Path :=
  let flag := store.read (writeInput refs.lessThan)
  let chosen := armStep refs flag store
  (chosen.1, ⟨flag, chosen.2⟩)

/-- Actual comparison followed by the stored-flag selection. -/
def into (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (compareOp refs)) (selectedInto refs)

/-- Complete actual store and chronological path record of saturating subtraction. -/
def step (refs : Refs ctx width) (store : Store ctx) : Store ctx × (into refs).Path :=
  Circuit.sequenceRecord (.classical (compareOp refs)) (selectedInto refs)
    (fun before => (before.applyOp (compareOp refs), ())) (selectedStep refs) store

/-- The selected instruction runs on the real store produced by comparison. -/
theorem step_store (refs : Refs ctx width) (store : Store ctx) :
    (step refs store).1 = (selectedStep refs (store.applyOp (compareOp refs))).1 := rfl

/-- The selected store is the actual charged clear or subtraction update. -/
theorem selectedStep_store (refs : Refs ctx width) (store : Store ctx) :
    (selectedStep refs store).1 =
      if (store.read (writeInput refs.lessThan)).toBool then store.applyOp (clearOp refs)
      else store.applyOp (subtractOp refs) := by
  unfold selectedStep
  cases stored : store.read (writeInput refs.lessThan) with
  | bit flag => cases flag <;> rfl

private theorem arm_execute (refs : Refs ctx width) (flag : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (arm refs flag).execute Reference state = state.mapClassical (fun entry =>
      ((armStep refs flag entry.1).1, (entry.2, (armStep refs flag entry.1).2))) := by
  cases flag with
  | bit flag =>
    cases flag
    all_goals
      refine (Circuit.execute_classical_mapClassical _ Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _

/-- Actual flag selection preserves every incoming history and quantum-reference block. -/
theorem selectedInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (selectedInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((selectedStep refs entry.1).1, (entry.2, (selectedStep refs entry.1).2))) :=
  Circuit.execute_branch_mapClassical (writeInput refs.lessThan) (arm refs)
    (armStep refs) (arm_execute refs) Reference state

/-- The actual circuit executes its exact record on the full incoming classical-quantum state. -/
theorem into_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into refs).execute Reference state = state.mapClassical (fun entry =>
      ((step refs entry.1).1, (entry.2, (step refs entry.1).2))) := by
  refine Circuit.execute_sequenceRecord (.classical (compareOp refs)) (selectedInto refs)
    (fun before => (before.applyOp (compareOp refs), ())) (selectedStep refs)
    ?_ (selectedInto_execute refs) Reference state
  intro reference history _ before
  refine (Circuit.execute_classical_mapClassical (compareOp refs) reference before).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSub
