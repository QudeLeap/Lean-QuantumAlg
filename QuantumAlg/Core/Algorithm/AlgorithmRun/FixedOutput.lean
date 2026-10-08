/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.AlgorithmRun
public import QuantumAlg.Core.Execution.CycleSchedule
public import QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.CycleSchedule.Cleanup.Deterministic
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# The same fixed physical seed on every actual output fiber

Full record grouping preserves the actual mass and arbitrary external
reference correlations, including zero-mass outcomes. The caller-prescribed
seed is transported through the same run; no replacement channel is used.
-/

namespace QuantumAlg.AlgorithmRun

noncomputable section

open Execution

attribute [local instance] Classical.decEq
attribute [local irreducible] ExecutionState.mapClassical

/-- Every real observed result has the fixed owned state established by the same actual code. -/
public theorem stateRequirement_of_reinitializedAt {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape resultShape : CShape}
    (actual : AlgorithmRun model pre post shape)
    (seed : post.quantumLayout.SelectedBasis post.borrowedSelectionᶜ)
    (fixed : Circuit.ReinitializedAt actual.code seed)
    (read : OutputRead post resultShape) {Reference : Register}
    (original : OracleInput model.classicalOracles pre Reference) :
    (StateRequirement.marginal post.borrowedSelectionᶜ read
      (fun _ _ => .pure (NormalizedVector.ket seed))).Holds original.caller
        (actual.finalState Reference original.state) := by
  intro value
  unfold AlgorithmRun.finalState
  rw [ExecutionState.executionState_mapClassical_comp]
  apply Circuit.RestartCleanup.selectedPureMapDecision post.quantumLayout
    post.borrowedSelectionᶜ Reference _ (actual.execute Reference original.state)
    (fun record => read.eval record.1) (NormalizedVector.ket seed) _ value
  intro record
  exact fixed Reference
    (original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))) record

end

end QuantumAlg.AlgorithmRun
