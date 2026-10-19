/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Model.BitWord.Execution
public import Mathlib.Logic.Function.Iterate
import all QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Core.Execution.Classical.Iteration

/-!
# Repeated execution of the selected native instruction

The existing circuit iteration reads the actual current store on every step.
Its finite path records each real native output at its chronological index.
The surrounding service state remains unchanged by these native operations;
all original caller, quantum and reference correlations are retained.
-/

namespace QuantumAlg.BitWord

noncomputable section

open Execution

attribute [local instance] Classical.decEq

variable {execution : ExecutionModel} {environment : execution.Environment} [Selected execution]
  {ctx : RuntimeCtx execution.kind} {input output : CShape}

/-- The actual finite repetition of one selected native leaf. -/
@[expose, implicit_reducible]
public def repeatInstruction (op : ClassicalOp input output ctx ctx) (count : Nat) :
    Circuit execution ctx ctx :=
  .iterate count (instruction (execution := execution) op)

/-- Actual final store and the native result produced at every finite stage. -/
public def repeatStep (op : ClassicalOp input output ctx ctx) (count : Nat) (store : Store ctx) :
    Store ctx × (repeatInstruction (execution := execution) op count).Path :=
  ((fun current => current.applyOp op)^[count] store,
    fun index : Fin count => (instructionStep (execution := execution) op
      ((fun current => current.applyOp op)^[index.val] store)).2)

private lemma iterate_keep_right {A B : Type} (step : A → A) (count : Nat)
    (left : A) (right : B) :
    (fun entry : A × B => (step entry.1, entry.2))^[count] (left, right) =
      (step^[count] left, right) := by
  induction count generalizing left with
  | zero => rfl
  | succ count ih =>
      simpa only [Function.iterate_succ_apply] using ih (step left)

/-- Real native repetition preserves the complete service and reference state with all outputs. -/
public lemma bitWord_repeatInstruction_execute (op : ClassicalOp input output ctx ctx)
    (count : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (execution.HiddenState × History)) :
    (repeatInstruction (execution := execution) op count).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := repeatStep (execution := execution) op count entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_iterate_mapClassical
    (environment := environment) (instruction (execution := execution) op)
    (fun before =>
      let result := instructionStep (execution := execution) op before.1
      ((result.1, before.2), result.2)) ?_ count Reference state).trans ?_
  · intro reference history _ input
    exact (bitWord_instruction_execute
      (environment := environment) (execution := execution) op input).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · apply ExecutionState.executionState_mapClassical_congr
    funext entry
    dsimp only [repeatStep, instructionStep]
    simp only [iterate_keep_right (fun current : Store ctx => current.applyOp op)]

end

end QuantumAlg.BitWord
