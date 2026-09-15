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

private theorem firstAdvanceArm_execute (refs : Refs ctx width) (flag : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (firstAdvanceArm refs flag).execute Reference state = state.mapClassical (fun entry =>
      ((firstAdvanceArmStep refs flag entry.1).1,
        (entry.2, (firstAdvanceArmStep refs flag entry.1).2))) := by
  cases flag with
  | bit flag =>
    cases flag
    · refine (Circuit.execute_id_mapClassical Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _
    · refine (LatticePhaseControl.transitionInto_execute refs.machine .firstPass Reference
      state).trans ?_
      congr 1
      exact Subsingleton.elim _ _

/-- The actual first Lovasz bit selects the matching full-state phase update. -/
theorem firstAdvanceInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (firstAdvanceInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((firstAdvanceStep refs entry.1).1, (entry.2, (firstAdvanceStep refs entry.1).2))) :=
  Circuit.execute_branch_mapClassical _ _ _ (firstAdvanceArm_execute refs) Reference state

/-- The actual first phase update and Gram refresh compose in the full state. -/
theorem firstTailInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (firstTailInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((firstTailStep refs entry.1).1, (entry.2, (firstTailStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (firstAdvanceInto refs)
    (LatticeMetricMachine.refreshInto refs.machine.basis refs.metric) (firstAdvanceStep refs)
    (fun store => (LatticeMetricMachine.refreshStore refs.machine.basis refs.metric store,
      LatticeMetricMachine.refreshPath refs.machine.basis refs.metric))
    (firstAdvanceInto_execute refs)
    (LatticeMetricMachine.refreshInto_execute refs.machine.basis refs.metric) Reference
      state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The actual first pair feeds its phase update and full Gram refresh in the complete state. -/
theorem firstStepInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (firstStepInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((firstStep refs entry.1).1, (entry.2, (firstStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (LatticeFirstPairMachine.firstPairInto refs.first)
    (firstTailInto refs) (LatticeFirstPairMachine.firstPairStep refs.first) (firstTailStep refs)
    (LatticeFirstPairMachine.firstPairInto_execute refs.first) (firstTailInto_execute refs)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

private theorem secondAdvanceArm_execute (refs : Refs ctx width) (flag : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (secondAdvanceArm refs flag).execute Reference state = state.mapClassical (fun entry =>
      ((secondAdvanceArmStep refs flag entry.1).1,
        (entry.2, (secondAdvanceArmStep refs flag entry.1).2))) := by
  cases flag with
  | bit flag =>
    cases flag
    · refine (LatticePhaseControl.transitionInto_execute refs.machine .secondFail Reference
      state).trans ?_
      congr 1
      exact Subsingleton.elim _ _
    · refine (LatticePhaseControl.transitionInto_execute refs.machine .secondPass Reference
      state).trans ?_
      congr 1
      exact Subsingleton.elim _ _

/-- The actual second Lovasz bit selects the matching full-state phase update. -/
theorem secondAdvanceInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (secondAdvanceInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((secondAdvanceStep refs entry.1).1, (entry.2, (secondAdvanceStep refs entry.1).2))) :=
  Circuit.execute_branch_mapClassical _ _ _ (secondAdvanceArm_execute refs) Reference state

/-- The actual second phase update and Gram refresh compose in the full state. -/
theorem secondTailInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (secondTailInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((secondTailStep refs entry.1).1, (entry.2, (secondTailStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (secondAdvanceInto refs)
    (LatticeMetricMachine.refreshInto refs.machine.basis refs.metric) (secondAdvanceStep refs)
    (fun store => (LatticeMetricMachine.refreshStore refs.machine.basis refs.metric store,
      LatticeMetricMachine.refreshPath refs.machine.basis refs.metric))
    (secondAdvanceInto_execute refs)
    (LatticeMetricMachine.refreshInto_execute refs.machine.basis refs.metric) Reference
      state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The actual second pair feeds its phase update and full Gram refresh in the complete state. -/
theorem secondStepInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (secondStepInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((secondStep refs entry.1).1, (entry.2, (secondStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (LatticeSecondPairFullMachine.secondPairInto refs.second)
    (secondTailInto refs) (LatticeSecondPairFullMachine.secondPairStep refs.second)
      (secondTailStep refs)
    (LatticeSecondPairFullMachine.secondPairInto_execute refs.second) (secondTailInto_execute refs)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

private theorem nonDoneArm_execute (refs : Refs ctx width) (flag : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (nonDoneArm refs flag).execute Reference state = state.mapClassical (fun entry =>
      ((nonDoneArmStep refs flag entry.1).1, (entry.2, (nonDoneArmStep refs flag entry.1).2))) := by
  cases flag with
  | bit flag =>
    cases flag
    · exact firstStepInto_execute refs Reference state
    · exact secondStepInto_execute refs Reference state

/-- The actual incoming phase bit selects the corresponding complete-state execution. -/
theorem nonDoneStepInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (nonDoneStepInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((nonDoneStep refs entry.1).1, (entry.2, (nonDoneStep refs entry.1).2))) :=
  Circuit.execute_branch_mapClassical _ _ _ (nonDoneArm_execute refs) Reference state

private theorem stepArm_execute (refs : Refs ctx width) (flag : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (stepArm refs flag).execute Reference state = state.mapClassical (fun entry =>
      ((stepArmStep refs flag entry.1).1, (entry.2, (stepArmStep refs flag entry.1).2))) := by
  cases flag with
  | bit flag =>
    cases flag
    · exact nonDoneStepInto_execute refs Reference state
    · refine (Circuit.execute_id_mapClassical Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _

/-- The actual incoming phase bit selects the corresponding complete-state execution. -/
theorem stepInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (stepInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((step refs entry.1).1, (entry.2, (step refs entry.1).2))) :=
  Circuit.execute_branch_mapClassical _ _ _ (stepArm_execute refs) Reference state

set_option maxHeartbeats 800000 in
-- Reconcile the finite path instances of all nested actual branches.
/-- Fixed-fuel execution retains the final store and chronological paths in the full state. -/
theorem fixedFuelInto_execute (fuel : Nat) (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (fixedFuelInto fuel refs).execute Reference state = state.mapClassical (fun entry =>
      ((fixedFuelStep fuel refs entry.1).1, (entry.2, (fixedFuelStep fuel refs entry.1).2))) := by
  refine (Circuit.execute_iterate_mapClassical _ _ (stepInto_execute refs) fuel Reference
    state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine
