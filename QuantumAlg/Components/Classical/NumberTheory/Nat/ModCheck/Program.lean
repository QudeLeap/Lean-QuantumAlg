/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.ModCheck.Layout
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Actual division followed by comparison of its stored remainder
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatModCheck

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {numeratorWidth divisorWidth : Nat}

/-- The original native division reads both input words before writing its pair. -/
def divideOp (refs : Refs ctx numeratorWidth divisorWidth) :=
  ClassicalOp.divRem numeratorWidth divisorWidth ctx
    (.product refs.numerator refs.divisor) refs.division

/-- Native equality compares the real stored remainder with the supplied zero input. -/
def checkOp (refs : Refs ctx numeratorWidth divisorWidth) :=
  ClassicalOp.wordBinary .equal divisorWidth ctx
    (.product (remainderInput refs) refs.zero) refs.accepted

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Actual native division followed by the stored-remainder comparison. -/
def into (refs : Refs ctx numeratorWidth divisorWidth) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (divideOp refs)) (BitWord.instruction (execution
    := model) (checkOp refs))

/-- Complete actual store and chronological pair of native instruction paths. -/
def step (refs : Refs ctx numeratorWidth divisorWidth) (store : Store ctx) :
    Store ctx × (into (model := model) refs).Path :=
  let division := BitWord.instructionStep (execution := model) (divideOp refs) store
  let checked := BitWord.instructionStep (execution := model) (checkOp refs) division.1
  (checked.1, (division.2, checked.2))

/-- The actual two-instruction circuit executes its full store and path record. -/
lemma into_execute (refs : Refs ctx numeratorWidth divisorWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) refs).execute environment Reference state
      = state.mapClassical (fun entry =>
      let actual := step (model := model) refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [into, step, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatModCheck
