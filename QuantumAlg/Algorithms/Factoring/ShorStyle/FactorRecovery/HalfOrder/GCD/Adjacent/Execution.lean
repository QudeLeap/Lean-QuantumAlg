/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Adjacent
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Complete store execution of the actual adjacent-word instructions

These records track the genuine widening, adjacent arithmetic and selected
underflow arm. Each theorem follows the existing circuit interpreter on its
entire store-history block and quantum-reference register.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeAdjacentWord

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {width : Nat}

/-- The actual selected arm leaves the word alone or performs its real self-XOR. -/
def trimArmStep (output : CWriteRef ctx (.unsignedWord (width + 1))) :
    (value : CShape.Value .bit) → Store ctx →
      Store ctx × (trimArm (model := model) output value).Path
  | .bit false, store => (store, ())
  | .bit true, store => BitWord.instructionStep (execution := model) (clearOp output) store

/-- Record the actual bit read, the selected path and its true store update. -/
def trimStep (output : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    Store ctx × (trim (model := model) output).Path :=
  let value := store.read (highBit output)
  let next := trimArmStep (model := model) output value store
  (next.1, ⟨value, next.2⟩)

/-- The two compile-time directions use their actual atomic or sequential paths. -/
def tailStep (output : CWriteRef ctx (.unsignedWord (width + 1))) :
    (successor : Bool) → Store ctx → Store ctx × (tail (model := model) successor output).Path
  | false, store =>
      let adjacent := BitWord.instructionStep (execution := model) (adjacentOp false output) store
      let next := trimStep (model := model) output adjacent.1
      (next.1, (adjacent.2, next.2))
  | true, store => BitWord.instructionStep (execution := model) (adjacentOp true output) store

/-- The actual complete adjacent-word record starts with its physical widening instruction. -/
def step (successor : Bool) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    Store ctx × (code (model := model) successor input output).Path :=
  let widened := BitWord.instructionStep (execution := model) (resizeOp input output) store
  let next := tailStep (model := model) output successor widened.1
  (next.1, (widened.2, next.2))

private theorem trimArm_execute (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (trimArm (model := model) output value).execute Reference state =
      state.mapClassical (fun entry => ((trimArmStep (model := model) output value entry.1).1,
        (entry.2.1, (entry.2.2, (trimArmStep (model := model) output value entry.1).2)))) := by
  cases value with
  | bit value =>
      cases value
      · refine (Circuit.execute_id_mapClassical Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl
      · refine (BitWord.bitWord_instruction_execute (clearOp output) state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual stored highest bit chooses the same complete store-reference execution. -/
theorem trim_execute (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (trim (model := model) output).execute Reference state =
      state.mapClassical (fun entry => ((trimStep (model := model) output entry.1).1,
        (entry.2.1, (entry.2.2, (trimStep (model := model) output entry.1).2)))) := by
  exact Circuit.execute_branch_mapClassical (highBit output) _
    (fun value entry =>
      let next := trimArmStep (model := model) output value entry.1
      ((next.1, entry.2), next.2))
    (trimArm_execute output) Reference state

/-- Both actual adjacent tails preserve every original quantum-reference matrix block. -/
theorem tail_execute (successor : Bool) (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (tail (model := model) successor output).execute Reference state =
      state.mapClassical (fun entry => ((tailStep (model := model) output successor entry.1).1,
        (entry.2.1, (entry.2.2, (tailStep (model := model) output successor entry.1).2)))) := by
  cases successor
  · change ((BitWord.instruction (execution := model) (adjacentOp false output)).seq
      (trim (model := model) output)).execute Reference state = _
    simp only [Circuit.execute_seq,
      BitWord.bitWord_instruction_execute, trim_execute, State.mapHistory,
      ExecutionState.executionState_mapClassical_comp, Function.comp_def]
    congr 1
    exact Subsingleton.elim _ _
  · refine (BitWord.bitWord_instruction_execute (adjacentOp true output) state).trans ?_
    exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual widening and the selected native tail compose on the unchanged complete register. -/
theorem code_execute (successor : Bool) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (code (model := model) successor input output).execute Reference state =
      state.mapClassical (fun entry => ((step (model := model) successor input output entry.1).1,
        (entry.2.1, (entry.2.2, (step (model := model) successor input output entry.1).2)))) := by
  simp only [code, Circuit.execute_seq, BitWord.bitWord_instruction_execute, tail_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeAdjacentWord
