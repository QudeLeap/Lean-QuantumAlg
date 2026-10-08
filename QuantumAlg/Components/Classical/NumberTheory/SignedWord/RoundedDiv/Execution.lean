/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Correctness

/-!
# Complete interpreter equations for signed nearest division

These equations connect the concrete chronological store updates to the one
circuit interpreter. They preserve the complete quantum-reference blocks and
prior history, and record each branch value actually read during execution.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Preparation executes the actual normalization and the three actual wider-word writes. -/
theorem prepare_execute (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (prepare (model := model) refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := prepareStep (model := model) refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [prepare, normalizeMagnitude, widenMagnitude, widenDenominator, prepareStep,
    Circuit.execute_seq, SignedWord.normalizeMagnitude_execute,
    BitWord.bitWord_instruction_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private theorem correctionChoice_execute (refs : BodyRefs ctx width)
    (flag : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (correctionChoice (model := model) refs flag).execute Reference state = state.mapClassical
      (fun entry =>
      let actual := correctionStep (model := model) refs flag entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  cases flag with
  | bit flag =>
      cases flag
      · exact (Circuit.execute_id_mapClassical Reference state).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)
      · exact BitWord.bitWord_instruction_execute _ state

private theorem correctionBranch_execute (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.branch (writeInput refs.negative)
      (correctionChoice (model := model) refs)).execute Reference state =
      state.mapClassical (fun entry =>
        let flag := entry.1.read (writeInput refs.negative)
        let actual := correctionStep (model := model) refs flag entry.1
        (actual.1, (entry.2.1, (entry.2.2, ⟨flag, actual.2⟩)))) := by
  refine (Circuit.execute_branch_mapClassical (writeInput refs.negative)
    (correctionChoice (model := model) refs)
    (fun flag before =>
      let actual := correctionStep (model := model) refs flag before.1
      ((actual.1, before.2), actual.2))
    (fun flag reference _history _ current => correctionChoice_execute refs flag reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Rounding follows the sign stored after the actual addition, with its full selected path. -/
theorem rounding_execute (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (roundingArm (model := model) refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := roundingStep (model := model) refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [roundingArm, roundingStep, Circuit.execute_seq,
    BitWord.bitWord_instruction_execute, correctionBranch_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private theorem restoreChoice_execute (refs : BodyRefs ctx width)
    (flag : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (restoreChoice (model := model) refs flag).execute Reference state = state.mapClassical (fun
      entry =>
      let actual := restoreStep (model := model) refs flag entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  cases flag with
  | bit flag =>
      cases flag
      · exact (Circuit.execute_id_mapClassical Reference state).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)
      · simp only [restoreChoice, restoreStep, Circuit.execute_seq,
          BitWord.bitWord_instruction_execute, State.mapHistory,
          ExecutionState.executionState_mapClassical_comp, Function.comp_def]
        exact ExecutionState.executionState_mapClassical_congr _ rfl

private theorem restoreBranch_execute (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.branch (writeInput refs.negative)
      (restoreChoice (model := model) refs)).execute Reference state =
      state.mapClassical (fun entry =>
        let flag := entry.1.read (writeInput refs.negative)
        let actual := restoreStep (model := model) refs flag entry.1
        (actual.1, (entry.2.1, (entry.2.2, ⟨flag, actual.2⟩)))) := by
  refine (Circuit.execute_branch_mapClassical (writeInput refs.negative)
    (restoreChoice (model := model) refs)
    (fun flag before =>
      let actual := restoreStep (model := model) refs flag before.1
      ((actual.1, before.2), actual.2))
    (fun flag reference _history _ current => restoreChoice_execute refs flag reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The final stage resizes the stored quotient and executes the branch read from its real flag. -/
theorem finish_execute (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (finish (model := model) refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := finishStep (model := model) refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [finish, finishStep, Circuit.execute_seq,
    BitWord.bitWord_instruction_execute, restoreBranch_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Complete actual execution of signed division on arbitrary histories and reference extensions. -/
theorem body_execute (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (body (model := model) refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := bodyStep (model := model) refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [body, bodyStep, divide, Circuit.execute_seq, prepare_execute, rounding_execute,
    finish_execute, BitWord.bitWord_instruction_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv
