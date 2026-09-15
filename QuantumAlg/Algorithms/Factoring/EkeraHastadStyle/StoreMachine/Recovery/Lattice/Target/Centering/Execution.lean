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

/-- Scratch initialization and the four original comparison instructions preserve the full state. -/
theorem prepareInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (prepareInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((prepareStep refs entry.1).1, (entry.2, (prepareStep refs entry.1).2))) := by
  simp only [prepareInto, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Actual complement and increment compose on the original full incoming execution state. -/
theorem negateInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (negateInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((negateStep refs entry.1).1, (entry.2, (negateStep refs entry.1).2))) := by
  simp only [negateInto, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Either actual half-comparison arm preserves the original reference correlations and history. -/
theorem halfArm_execute (refs : Refs ctx width) (flag : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (halfArm refs flag).execute Reference state = state.mapClassical (fun entry =>
      ((halfArmStep refs flag entry.1).1, (entry.2, (halfArmStep refs flag entry.1).2))) := by
  cases flag with
  | bit flag =>
    cases flag
    · refine (Circuit.execute_classical_mapClassical (subOp refs refs.modulus refs.a)
        Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _
    · exact negateInto_execute refs Reference state

/-- The actual stored half-comparison value selects the arithmetic executed in the full state. -/
theorem halfInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (halfInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((halfStep refs entry.1).1, (entry.2, (halfStep refs entry.1).2))) :=
  Circuit.execute_branch_mapClassical _ _ _ (halfArm_execute refs) Reference state

/-- Either actual zero-test arm retains the complete original quantum-reference state. -/
theorem finishArm_execute (refs : Refs ctx width) (flag : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (finishArm refs flag).execute Reference state = state.mapClassical (fun entry =>
      ((finishArmStep refs flag entry.1).1, (entry.2, (finishArmStep refs flag entry.1).2))) := by
  cases flag with
  | bit flag =>
    cases flag
    · exact halfInto_execute refs Reference state
    · refine (Circuit.execute_classical_mapClassical (subOp refs refs.a refs.a)
        Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _

/-- The actual stored zero-test value selects the arithmetic executed in the full state. -/
theorem finishInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (finishInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((finishStep refs entry.1).1, (entry.2, (finishStep refs entry.1).2))) :=
  Circuit.execute_branch_mapClassical _ _ _ (finishArm_execute refs) Reference state

/-- Actual stored comparisons feed the complete selected arithmetic in the original full state. -/
theorem centeredTargetInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (centeredTargetInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((centeredTargetStep refs entry.1).1, (entry.2, (centeredTargetStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (prepareInto refs) (finishInto refs)
    (prepareStep refs) (finishStep refs) (prepareInto_execute refs) (finishInto_execute refs)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTarget
