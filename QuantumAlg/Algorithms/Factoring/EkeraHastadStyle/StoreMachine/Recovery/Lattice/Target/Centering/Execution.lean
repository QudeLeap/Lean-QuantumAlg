/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Centering

/-!
# Full actual centered-target execution

The actual initialized comparison store feeds each original stored-bit branch.
Every selected arithmetic arm composes on the chronological store while the
whole original history and quantum-reference blocks remain present.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTarget

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Scratch initialization and the four original comparison instructions preserve the full state. -/
lemma prepareInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (prepareInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := prepareStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [prepareInto, prepareStep, Circuit.execute_seq,
    BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual complement and increment compose on the original full incoming execution state. -/
lemma negateInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (negateInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := negateStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [negateInto, negateStep, Circuit.execute_seq,
    BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Either actual half-comparison arm preserves the original reference correlations and history. -/
lemma halfArm_execute (refs : Refs ctx width) (flag : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (halfArm refs flag).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := halfArmStep refs flag entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  cases flag with
  | bit flag =>
    cases flag
    · exact BitWord.bitWord_instruction_execute (environment := environment) _ state
    · exact negateInto_execute refs Reference state

/-- The actual stored half-comparison value selects the arithmetic executed in the full state. -/
lemma halfInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (halfInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := halfStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_branch_mapClassical
    (environment := environment) (writeInput refs.belowHalf)
    (halfArm refs)
    (fun flag before =>
      let actual := halfArmStep refs flag before.1
      ((actual.1, before.2), actual.2))
    (fun flag reference _history _ current => halfArm_execute refs flag reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Either actual zero-test arm retains the complete original quantum-reference state. -/
lemma finishArm_execute (refs : Refs ctx width) (flag : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (finishArm refs flag).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := finishArmStep refs flag entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  cases flag with
  | bit flag =>
    cases flag
    · exact halfInto_execute refs Reference state
    · exact BitWord.bitWord_instruction_execute (environment := environment) _ state

/-- The actual stored zero-test value selects the arithmetic executed in the full state. -/
lemma finishInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (finishInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := finishStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_branch_mapClassical (environment := environment) (writeInput refs.isZero)
    (finishArm refs)
    (fun flag before =>
      let actual := finishArmStep refs flag before.1
      ((actual.1, before.2), actual.2))
    (fun flag reference _history _ current => finishArm_execute refs flag reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual stored comparisons feed the complete selected arithmetic in the original full state. -/
lemma centeredTargetInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (centeredTargetInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := centeredTargetStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (environment := environment) (prepareInto refs) (finishInto refs)
    (fun before =>
      let actual := prepareStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := finishStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => prepareInto_execute refs reference current)
    (fun reference _history _ current => finishInto_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTarget
