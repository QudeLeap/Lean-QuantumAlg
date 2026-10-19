/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Interpret.Laws
import QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Actual deterministic tails after arbitrary circuit execution

The first circuit may prepare or transform quantum systems and measure into
real classical cells. A proved deterministic tail retains a classical result
cell and processes precisely those
final stores. Its complete interpreter equation therefore maps the existing
first-circuit blocks and appends the actual tail path, retaining all quantum
and reference correlations. No outcome distribution is supplied separately.
-/

namespace QuantumAlg.Circuit

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A proved deterministic tail maps the actual preceding execution and its original history. -/
lemma execute_seq_retained_mapClassical_tail {model : ExecutionModel}
    {pre middle : RuntimeCtx model.kind} (key : StorageKey) (shape : CShape)
    (fresh : key ∉ middle.keys)
    (first : Circuit model pre middle)
    (second : Circuit model middle (middle.addRetained key shape fresh))
    (environment : model.Environment)
    (step : Store middle × model.HiddenState →
      (Store (middle.addRetained key shape fresh) × model.HiddenState) × second.Path)
    (secondEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State middle Reference (model.HiddenState × History)),
      second.execute environment Reference state = state.mapClassical (fun entry =>
        let result := step (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State pre Reference (model.HiddenState × History)) :
    (Circuit.seq first second).execute environment Reference state =
      (first.execute environment Reference state).mapClassical (fun entry =>
        let result := step (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2.1, (entry.2.2.2, result.2))))) := by
  rw [execute_seq, secondEquation]
  dsimp only [State.mapHistory]
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Circuit
