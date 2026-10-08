/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Initialize.Program
import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Rounds.Program
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Actual initialization, finite refinement and caller-visible square-root copy
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt

open Execution
open IntegerSqrt (writeInput)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {inputWidth : Nat}

/-- Native copy from the final lower endpoint into the caller-visible output. -/
def finishOp (refs : Refs ctx inputWidth) :=
  ClassicalOp.wordUnary .copy (workWidth inputWidth) ctx
    (writeInput refs.round.root) refs.output

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The final actual caller-output write. -/
def finishInto (refs : Refs ctx inputWidth) : Circuit model ctx ctx := BitWord.instruction
  (execution := model) (finishOp refs)

/-- Actual output-write store and single native path. -/
def finishStep (refs : Refs ctx inputWidth) (store : Store ctx) :
    Store ctx × (finishInto (model := model) refs).Path := BitWord.instructionStep (execution :=
      model) (finishOp refs) store

private theorem finishInto_execute (refs : Refs ctx inputWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (finishInto (model := model) refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := finishStep (model := model) refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  exact BitWord.bitWord_instruction_execute _ state

/-- The exact finite refinement followed by the actual final output copy. -/
def refineInto (refs : Refs ctx inputWidth) : Circuit model ctx ctx :=
  .seq (roundsInto (model := model) refs inputWidth) (finishInto (model := model) refs)

/-- Chronological record of refinement and the final caller-output write. -/
def refineStep (refs : Refs ctx inputWidth) (store : Store ctx) :
    Store ctx × (refineInto (model := model) refs).Path :=
  let refined := roundsStep (model := model) refs inputWidth store
  let finished := finishStep (model := model) refs refined.1
  (finished.1, (refined.2, finished.2))

private theorem refineInto_execute (refs : Refs ctx inputWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (refineInto (model := model) refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := refineStep (model := model) refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [refineInto, refineStep, Circuit.execute_seq, roundsInto_execute,
    finishInto_execute, State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Complete actual natural-square-root driver on the original caller-supplied cells. -/
def into (refs : Refs ctx inputWidth) : Circuit model ctx ctx :=
  .seq (initializeInto (model := model) refs) (refineInto (model := model) refs)

/-- Complete actual driver record, including all initialization and branch-dependent paths. -/
def step (refs : Refs ctx inputWidth) (store : Store ctx) :
    Store ctx × (into (model := model) refs).Path :=
  let initialized := initializeStep (model := model) refs store
  let refined := refineStep (model := model) refs initialized.1
  (refined.1, (initialized.2, refined.2))

/-- The returned caller store is the actual copy after initialization and every refinement. -/
theorem step_store (refs : Refs ctx inputWidth) (store : Store ctx) :
    (step (model := model) refs store).1 =
      (roundsStep (model := model) refs inputWidth (initializeStep (model := model) refs
        store).1).1.applyOp (finishOp refs) := rfl

/-- The actual driver retains the full incoming classical history and quantum-reference state. -/
theorem into_execute (refs : Refs ctx inputWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := step (model := model) refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [into, step, Circuit.execute_seq, initializeInto_execute,
    refineInto_execute, State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt
