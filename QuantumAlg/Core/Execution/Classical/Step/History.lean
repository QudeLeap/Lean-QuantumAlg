/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Step
public import QuantumAlg.Core.Execution.Random.Kernel.Map
import all QuantumAlg.Core.Execution.Classical.Step
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Declared classical execution through mathematical history maps

Only the mathematical history is grouped. Native instructions still read and
write their actual store. Queries retain their actual current/next hidden state,
and their declared transition is evaluated exactly once per call. Noninjective
history maps sum full correlated quantum blocks without renormalizing them.
-/

namespace QuantumAlg.Execution.State

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {H K : Type} [Fintype H] [Fintype K]

/-- Native execution is independent of how the prior mathematical history is grouped. -/
theorem mapHistory_nativeStep {model : ClassicalOpModel} (application : model.Application ctx)
    (state : State ctx Reference H) (update : H → K) :
    nativeStep application (state.mapHistory update) =
      (nativeStep application state).mapHistory (fun record => (update record.1, record.2)) := by
  dsimp only [nativeStep, mapHistory]
  rw [kernelChoice_mapClassical (afterMap := inferInstance)]
  dsimp only [Function.comp_def]
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance),
    ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Grouping history never groups, resets or reinitializes the query's persistent state. -/
theorem mapHistory_queryStep {model : ClassicalOracleModel} (application : model.Application ctx)
    (state : State ctx Reference (model.HiddenState × H)) (update : H → K) :
    queryStep application (state.mapHistory (fun record => (record.1, update record.2))) =
      (queryStep application state).mapHistory
        (fun record => (record.1, (update record.2.1, record.2.2))) := by
  dsimp only [queryStep, mapHistory]
  rw [kernelChoice_mapClassical (afterMap := inferInstance)]
  dsimp only [Function.comp_def]
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance),
    ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Execution.State
