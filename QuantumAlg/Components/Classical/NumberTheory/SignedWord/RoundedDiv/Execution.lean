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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Preparation executes the actual normalization and the three actual wider-word writes. -/
theorem prepare_execute (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (prepare refs).execute Reference state = state.mapClassical (fun entry =>
      ((prepareStep refs entry.1).1, (entry.2, (prepareStep refs entry.1).2))) := by
  simp only [prepare, normalizeMagnitude, widenMagnitude, widenDenominator, prepareStep,
    Circuit.execute_seq, SignedWord.normalizeMagnitude_execute,
    Circuit.execute_classical_mapClassical, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

private theorem correctionChoice_execute (refs : BodyRefs ctx width)
    (flag : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (correctionChoice refs flag).execute Reference state = state.mapClassical (fun entry =>
      ((correctionStep refs flag entry.1).1, (entry.2, (correctionStep refs flag entry.1).2))) := by
  cases flag with
  | bit flag =>
      cases flag <;>
        simp only [correctionChoice, correctionStep, Circuit.execute_id_mapClassical,
          Circuit.execute_classical_mapClassical] <;>
        congr 1 <;> exact Subsingleton.elim _ _

private theorem correctionBranch_execute (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.branch (writeInput refs.negative) (correctionChoice refs)).execute Reference state =
      state.mapClassical (fun entry =>
        ((correctionStep refs (entry.1.read (writeInput refs.negative)) entry.1).1,
          (entry.2, ⟨entry.1.read (writeInput refs.negative),
            (correctionStep refs (entry.1.read (writeInput refs.negative)) entry.1).2⟩))) := by
  exact Circuit.execute_branch_mapClassical _ _ _ (correctionChoice_execute refs) Reference state

/-- Rounding follows the sign stored after the actual addition, with its full selected path. -/
theorem rounding_execute (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (roundingArm refs).execute Reference state = state.mapClassical (fun entry =>
      ((roundingStep refs entry.1).1, (entry.2, (roundingStep refs entry.1).2))) := by
  simp only [roundingArm, roundingStep, Circuit.execute_seq,
    Circuit.execute_classical_mapClassical, correctionBranch_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

private theorem restoreChoice_execute (refs : BodyRefs ctx width)
    (flag : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (restoreChoice refs flag).execute Reference state = state.mapClassical (fun entry =>
      ((restoreStep refs flag entry.1).1, (entry.2, (restoreStep refs flag entry.1).2))) := by
  cases flag with
  | bit flag =>
      cases flag <;>
        simp only [restoreChoice, restoreStep, Circuit.execute_id_mapClassical,
          Circuit.execute_seq, Circuit.execute_classical_mapClassical, State.mapHistory,
          ExecutionState.executionState_mapClassical_comp, Function.comp_def] <;>
        congr 1 <;> exact Subsingleton.elim _ _

private theorem restoreBranch_execute (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.branch (writeInput refs.negative) (restoreChoice refs)).execute Reference state =
      state.mapClassical (fun entry =>
        ((restoreStep refs (entry.1.read (writeInput refs.negative)) entry.1).1,
          (entry.2, ⟨entry.1.read (writeInput refs.negative),
            (restoreStep refs (entry.1.read (writeInput refs.negative)) entry.1).2⟩))) := by
  exact Circuit.execute_branch_mapClassical _ _ _ (restoreChoice_execute refs) Reference state

/-- The final stage resizes the stored quotient and executes the branch read from its real flag. -/
theorem finish_execute (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (finish refs).execute Reference state = state.mapClassical (fun entry =>
      ((finishStep refs entry.1).1, (entry.2, (finishStep refs entry.1).2))) := by
  simp only [finish, finishStep, Circuit.execute_seq,
    Circuit.execute_classical_mapClassical, restoreBranch_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Complete actual execution of signed division on arbitrary histories and reference extensions. -/
theorem body_execute (refs : BodyRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (body refs).execute Reference state = state.mapClassical (fun entry =>
      ((bodyStep refs entry.1).1, (entry.2, (bodyStep refs entry.1).2))) := by
  simp only [body, bodyStep, divide, Circuit.execute_seq, prepare_execute, rounding_execute,
    finish_execute, Circuit.execute_classical_mapClassical, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv
