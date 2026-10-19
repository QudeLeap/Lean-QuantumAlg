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
# Actual deterministic processing after retained allocation

The circuit first allocates its real retained cell and then executes a body
whose actual store-and-path equation has been proved. Composition preserves
the same density blocks and reference correlations, adding only the genuine
allocation path to the body's actual record. This is a law of the existing
interpreter, with no alternative instruction or probability carrier.
-/

namespace QuantumAlg.Circuit

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A real retained allocation composes with a proved actual deterministic body record. -/
lemma execute_retain_seq_mapClassical {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit model (ctx.addRetained key shape fresh) (ctx.addRetained key shape fresh))
    (environment : model.Environment)
    (step : Store (ctx.addRetained key shape fresh) × model.HiddenState →
      (Store (ctx.addRetained key shape fresh) × model.HiddenState) × body.Path)
    (bodyEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (ctx.addRetained key shape fresh) Reference (model.HiddenState × History)),
      body.execute environment Reference state = state.mapClassical (fun entry =>
        let result := step (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (.retain ctx key shape fresh) body).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := step (entry.1.pushRetained key shape fresh, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, ((), result.2))))) := by
  rw [execute_seq, bodyEquation, execute_retain]
  dsimp only [State.mapHistory]
  erw [ExecutionState.executionState_mapClassical_comp_instances
      (R := Register.prod ctx.register Reference) (result := inferInstance),
    ExecutionState.executionState_mapClassical_comp_instances
      (R := Register.prod ctx.register Reference) (result := inferInstance)]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Circuit
