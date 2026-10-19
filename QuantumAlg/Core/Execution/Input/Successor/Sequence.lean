/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Input.Successor.Distribution
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# Exact actual inputs across sequential circuit sections

Forgetting path records at a section boundary commutes with subsequent
execution. The store, persistent service and full quantum-reference state
are retained; no fresh service, physical reset or normalization is inserted.
-/

namespace QuantumAlg.Circuit

variable {allowAllocation : Bool}

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma oracleInput_eq_of_state_eq {oracles : ClassicalOracleModel}
    {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
    (first second : OracleInput oracles ctx Reference) (same : first.state = second.state) :
    first = second := by
  cases first
  cases second
  cases same
  rfl

/-- A real sequential execution supplies the same complete successor input
as projecting the first section's history before executing the second. -/
lemma nextInput_seq {model : ExecutionModel}
    {pre middle post : RuntimeCtx model.kind}
    (first : Circuit model pre middle allowAllocation) (second : Circuit model middle post
      allowAllocation) (environment : model.Environment)
    {Reference : Register} (input : OracleInput model.classicalOracles pre Reference) :
    (first.seq second).nextInput environment input =
      second.nextInput environment (first.nextInput environment input) := by
  apply oracleInput_eq_of_state_eq
  let entered := input.state.mapClassical (fun value => (value.1, (value.2, ())))
  let prior := first.execute environment Reference entered
  have nextEntered :
      (first.nextInput environment input).state.mapClassical
          (fun value => (value.1, (value.2, ()))) =
        prior.mapHistory (fun history => (history.1, ())) := by
    simp only [nextInput, State.mapHistory, ExecutionState.executionState_mapClassical_comp,
      Function.comp_def, prior, entered]
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _
      (fun _ => rfl) _ _
  have rightState : (second.nextInput environment (first.nextInput environment input)).state =
      (second.execute environment Reference prior).mapClassical
        (fun record => (record.1, record.2.1)) := by
    change (second.execute environment Reference
      ((first.nextInput environment input).state.mapClassical
        (fun value => (value.1, (value.2, ()))))).mapClassical
          (fun record => (record.1, record.2.1)) = _
    rw [nextEntered,
      Circuit.execute_mapHistory second environment Reference prior
        (fun _ : Unit × first.Path => ())]
    dsimp only [State.mapHistory]
    rw [ExecutionState.executionState_mapClassical_comp_instances (result := Classical.decEq _)]
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _
      (fun _ => rfl) _ _
  rw [rightState]
  change ((first.seq second).execute environment Reference entered).mapClassical
    (fun record => (record.1, record.2.1)) = _
  rw [Circuit.execute_seq]
  dsimp only [State.mapHistory]
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := Classical.decEq _)]
  exact ExecutionState.executionState_mapClassical_congr_decision _ _ _
    (fun _ => rfl) _ _

/-- The terminal identity contributes only an erased history marker. Its
actual successor input has precisely the same joint caller/service state. -/
lemma nextInput_seq_identity_state {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) {pre : RuntimeCtx model.kind}
    (code : Circuit model pre ctx allowAllocation)
    (environment : model.Environment) {Reference : Register}
    (original : Execution.OracleInput model.classicalOracles pre Reference) :
    ((code.seq (Circuit.id (model := model) ctx)).nextInput environment original).state =
      (code.nextInput environment original).state := by
  change
    (((code.seq (Circuit.id (model := model) ctx)).execute environment Reference
      (original.state.mapClassical (fun entry => (entry.1, (entry.2, ()))))).mapClassical
        (fun record => (record.1, record.2.1))) =
    ((code.execute environment Reference
      (original.state.mapClassical (fun entry => (entry.1, (entry.2, ()))))).mapClassical
        (fun record => (record.1, record.2.1)))
  rw [execute_seq, execute_id_mapClassical]
  dsimp only [Execution.State.mapHistory]
  rw [ExecutionState.executionState_mapClassical_comp_instances
      (result := Classical.decEq _),
    ExecutionState.executionState_mapClassical_comp_instances
      (result := Classical.decEq _)]
  exact ExecutionState.executionState_mapClassical_congr_decision _ _ _
    (fun _ => rfl) _ _

end

end QuantumAlg.Circuit
