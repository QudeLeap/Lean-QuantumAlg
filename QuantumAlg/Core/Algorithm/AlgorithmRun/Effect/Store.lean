/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.State.History
import all QuantumAlg.Core.Execution.Borrowed.Support

/-!
# Store observations across the actual algorithm's input history

The algorithm run retains the original Store for relational correctness.
An observable of the final Store alone is unchanged if that mathematical
history is forgotten. Both sides execute the same physical circuit and
retain every complete quantum-reference block.
-/

namespace QuantumAlg.AlgorithmRun

variable {allowAllocation : Bool}

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- An actual run's final-Store effect weight equals the same circuit's
effect weight on the unit-history input, without changing the physical run. -/
lemma storedEffectWeight_eq_code_skip
    {model : ExecutionModel} {pre post : RuntimeCtx model.kind} {shape : CShape}
    (run : AlgorithmRun model pre post shape allowAllocation)
    (environment : model.Environment) {Reference : Register}
    (input : OracleInput model.classicalOracles pre Reference)
    (effects : Store post → Effect (post.register.prod Reference)) :
    (run.execute environment Reference input.state).effectWeight (fun record => effects record.1) =
      ((run.code.execute environment Reference (State.skip input.state)).effectWeight
        (fun record => effects record.1)) := by
  let recorded : State pre Reference (model.HiddenState × Store pre) :=
    input.state.mapClassical (fun value => (value.1, (value.2, value.1)))
  have runEq : run.execute environment Reference input.state =
      run.code.execute environment Reference recorded := by
    unfold AlgorithmRun.execute
    exact congrArg (run.code.execute environment Reference)
      (ExecutionState.executionState_mapClassical_congr_decision input.state
        (fun value => (value.1, (value.2, value.1)))
        (fun value => (value.1, (value.2, value.1))) (by intro; rfl) _ _)
  have enteredEq :
      recorded.mapHistory (fun history => (history.1, ())) =
        State.skip input.state := by
    dsimp only [recorded, State.mapHistory, State.skip]
    rw [ExecutionState.executionState_mapClassical_comp_instances
      (result := inferInstance)]
    exact ExecutionState.executionState_mapClassical_congr_decision input.state
      (fun value => (value.1, (value.2, ())))
      (fun value => (value.1, (value.2, ()))) (by intro; rfl) _ _
  calc
    (run.execute environment Reference input.state).effectWeight (fun record => effects record.1) =
        (run.code.execute environment Reference recorded).effectWeight
          (fun record => effects record.1) := by rw [runEq]
    _ = ((run.code.execute environment Reference recorded).mapHistory
          (fun history => (history.1, ((), history.2.2)))).effectWeight
            (fun record => effects record.1) := by
      rw [State.effectWeight_mapHistory]
    _ = (run.code.execute environment Reference
          (recorded.mapHistory (fun history => (history.1, ())))).effectWeight
            (fun record => effects record.1) := by
      erw [Circuit.execute_mapHistory run.code environment Reference recorded
        (fun _ : Store pre => ())]
    _ = (run.code.execute environment Reference (State.skip input.state)).effectWeight
          (fun record => effects record.1) := by rw [enteredEq]

end

end QuantumAlg.AlgorithmRun
