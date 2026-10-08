/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Program

/-!
# Full-state equations for the actual fixed-fuel LLL driver

Every branch is selected by its incoming store, and every stage consumes the
store produced by its predecessor. The complete interpreter equation retains
every quantum-reference block, history, and actual iteration path.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

private theorem firstAdvanceArm_execute (refs : Refs ctx width) (flag : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (firstAdvanceArm (model := model) refs flag).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := firstAdvanceArmStep (model := model) refs flag entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  cases flag with
  | bit flag =>
    cases flag
    · refine (Circuit.execute_id_mapClassical Reference state).trans ?_
      exact ExecutionState.executionState_mapClassical_congr _ rfl
    · exact LatticePhaseControl.transitionInto_execute refs.machine .firstPass
        Reference state

/-- The actual first Lovasz bit selects the matching full-state phase update. -/
theorem firstAdvanceInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (firstAdvanceInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := firstAdvanceStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_branch_mapClassical
    (.storage refs.first.lovasz.passes.toCStorageRef)
    (firstAdvanceArm (model := model) refs)
    (fun flag before =>
      let actual := firstAdvanceArmStep (model := model) refs flag before.1
      ((actual.1, before.2), actual.2))
    (fun flag reference _history _ current =>
      firstAdvanceArm_execute refs flag reference current) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual first phase update and Gram refresh compose in the full state. -/
theorem firstTailInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (firstTailInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := firstTailStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (firstAdvanceInto (model := model) refs)
    (LatticeMetricMachine.refreshInto (model := model) refs.machine.basis refs.metric)
    (fun before =>
      let actual := firstAdvanceStep (model := model) refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeMetricMachine.refreshStep (model := model)
        refs.machine.basis refs.metric before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => firstAdvanceInto_execute refs reference current)
    (fun reference _history _ current =>
      LatticeMetricMachine.refreshInto_execute refs.machine.basis refs.metric
        reference current) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual first pair feeds its phase update and full Gram refresh in the complete state. -/
theorem firstStepInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (firstStepInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := firstStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeFirstPairMachine.firstPairInto (model := model) refs.first)
    (firstTailInto (model := model) refs)
    (fun before =>
      let actual := LatticeFirstPairMachine.firstPairStep (model := model)
        refs.first before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := firstTailStep (model := model) refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      LatticeFirstPairMachine.firstPairInto_execute refs.first reference current)
    (fun reference _history _ current => firstTailInto_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private theorem secondAdvanceArm_execute (refs : Refs ctx width) (flag : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (secondAdvanceArm (model := model) refs flag).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := secondAdvanceArmStep (model := model) refs flag entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  cases flag with
  | bit flag =>
    cases flag
    · exact LatticePhaseControl.transitionInto_execute refs.machine .secondFail
        Reference state
    · exact LatticePhaseControl.transitionInto_execute refs.machine .secondPass
        Reference state

/-- The actual second Lovasz bit selects the matching full-state phase update. -/
theorem secondAdvanceInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (secondAdvanceInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := secondAdvanceStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_branch_mapClassical
    (.storage refs.second.branch.lovasz.passes.toCStorageRef)
    (secondAdvanceArm (model := model) refs)
    (fun flag before =>
      let actual := secondAdvanceArmStep (model := model) refs flag before.1
      ((actual.1, before.2), actual.2))
    (fun flag reference _history _ current =>
      secondAdvanceArm_execute refs flag reference current) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual second phase update and Gram refresh compose in the full state. -/
theorem secondTailInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (secondTailInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := secondTailStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (secondAdvanceInto (model := model) refs)
    (LatticeMetricMachine.refreshInto (model := model) refs.machine.basis refs.metric)
    (fun before =>
      let actual := secondAdvanceStep (model := model) refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeMetricMachine.refreshStep (model := model)
        refs.machine.basis refs.metric before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => secondAdvanceInto_execute refs reference current)
    (fun reference _history _ current =>
      LatticeMetricMachine.refreshInto_execute refs.machine.basis refs.metric
        reference current) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual second pair feeds its phase update and full Gram refresh in the complete state. -/
theorem secondStepInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (secondStepInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := secondStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeSecondPairFullMachine.secondPairInto (model := model) refs.second)
    (secondTailInto (model := model) refs)
    (fun before =>
      let actual := LatticeSecondPairFullMachine.secondPairStep (model := model)
        refs.second before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := secondTailStep (model := model) refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      LatticeSecondPairFullMachine.secondPairInto_execute refs.second reference current)
    (fun reference _history _ current => secondTailInto_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private theorem nonDoneArm_execute (refs : Refs ctx width) (flag : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (nonDoneArm (model := model) refs flag).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := nonDoneArmStep (model := model) refs flag entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  cases flag with
  | bit flag =>
    cases flag
    · exact firstStepInto_execute refs Reference state
    · exact secondStepInto_execute refs Reference state

/-- The actual incoming phase bit selects the corresponding complete-state execution. -/
theorem nonDoneStepInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (nonDoneStepInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := nonDoneStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_branch_mapClassical (phaseInput refs.machine.secondPhase)
    (nonDoneArm (model := model) refs)
    (fun flag before =>
      let actual := nonDoneArmStep (model := model) refs flag before.1
      ((actual.1, before.2), actual.2))
    (fun flag reference _history _ current =>
      nonDoneArm_execute refs flag reference current) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private theorem stepArm_execute (refs : Refs ctx width) (flag : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (stepArm (model := model) refs flag).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := stepArmStep (model := model) refs flag entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  cases flag with
  | bit flag =>
    cases flag
    · exact nonDoneStepInto_execute refs Reference state
    · refine (Circuit.execute_id_mapClassical Reference state).trans ?_
      exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual incoming phase bit selects the corresponding complete-state execution. -/
theorem stepInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (stepInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := step (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_branch_mapClassical (phaseInput refs.machine.done)
    (stepArm (model := model) refs)
    (fun flag before =>
      let actual := stepArmStep (model := model) refs flag before.1
      ((actual.1, before.2), actual.2))
    (fun flag reference _history _ current =>
      stepArm_execute refs flag reference current) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

set_option maxHeartbeats 800000 in
-- Reconcile the finite path instances of all nested actual branches.
/-- Fixed-fuel execution retains the final store and chronological paths in the full state. -/
theorem fixedFuelInto_execute (fuel : Nat) (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (fixedFuelInto (model := model) fuel refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := fixedFuelStep (model := model) fuel refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  let jointStep := fun before : Store ctx × model.HiddenState =>
    let actual := step (model := model) refs before.1
    ((actual.1, before.2), actual.2)
  have iterateJoint (steps : Nat) (store : Store ctx) (hidden : model.HiddenState) :
      (fun before => (jointStep before).1)^[steps] (store, hidden) =
        ((fun current => (step (model := model) refs current).1)^[steps] store,
          hidden) := by
    induction steps with
    | zero => rfl
    | succ steps inductionHypothesis =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          inductionHypothesis]
  refine (Circuit.execute_iterate_mapClassical (stepInto (model := model) refs)
    jointStep (fun reference _history _ current => stepInto_execute refs reference current)
    fuel Reference state).trans ?_
  apply ExecutionState.executionState_mapClassical_congr
  funext entry
  simp only [fixedFuelStep, iterateJoint, jointStep]
  rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine
