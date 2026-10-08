/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.CycleSchedule.InputDistribution
import all QuantumAlg.Core.Execution.Circuit.History

/-!
# Exact actual inputs across sequential circuit sections

Forgetting path records at a section boundary commutes with subsequent
execution. The store, persistent service and full quantum-reference state
are retained; no fresh service, physical reset or normalization is inserted.
-/

namespace QuantumAlg.Circuit

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem oracleInput_eq_of_state_eq {oracles : ClassicalOracleModel}
    {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
    (first second : OracleInput oracles ctx Reference) (same : first.state = second.state) :
    first = second := by
  cases first
  cases second
  cases same
  rfl

/-- A real sequential execution supplies the same complete successor input
as projecting the first section's history before executing the second. -/
theorem nextInput_seq {model : ExecutionModel}
    {pre middle post : RuntimeCtx model.kind}
    (first : Circuit model pre middle) (second : Circuit model middle post)
    {Reference : Register} (input : OracleInput model.classicalOracles pre Reference) :
    (first.seq second).nextInput input = second.nextInput (first.nextInput input) := by
  apply oracleInput_eq_of_state_eq
  let entered := input.state.mapClassical (fun value => (value.1, (value.2, ())))
  let prior := first.execute Reference entered
  have nextEntered :
      (first.nextInput input).state.mapClassical
          (fun value => (value.1, (value.2, ()))) =
        prior.mapHistory (fun history => (history.1, ())) := by
    simp only [nextInput, State.mapHistory, ExecutionState.executionState_mapClassical_comp,
      Function.comp_def, prior, entered]
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _
      (fun _ => rfl) _ _
  have rightState : (second.nextInput (first.nextInput input)).state =
      (second.execute Reference prior).mapClassical
        (fun record => (record.1, record.2.1)) := by
    change (second.execute Reference
      ((first.nextInput input).state.mapClassical
        (fun value => (value.1, (value.2, ()))))).mapClassical
          (fun record => (record.1, record.2.1)) = _
    rw [nextEntered,
      Circuit.execute_mapHistory second Reference prior (fun _ : Unit × first.Path => ())]
    dsimp only [State.mapHistory]
    rw [ExecutionState.executionState_mapClassical_comp_instances (result := Classical.decEq _)]
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _
      (fun _ => rfl) _ _
  rw [rightState]
  change ((first.seq second).execute Reference entered).mapClassical
    (fun record => (record.1, record.2.1)) = _
  rw [Circuit.execute_seq]
  dsimp only [State.mapHistory]
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := Classical.decEq _)]
  exact ExecutionState.executionState_mapClassical_congr_decision _ _ _
    (fun _ => rfl) _ _

end

end QuantumAlg.Circuit
