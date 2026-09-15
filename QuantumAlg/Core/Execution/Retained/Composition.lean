/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Interpret.Laws
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
theorem execute_retain_seq_mapClassical {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit (ctx.addRetained key shape fresh) (ctx.addRetained key shape fresh))
    (step : Store (ctx.addRetained key shape fresh) →
      Store (ctx.addRetained key shape fresh) × body.Path)
    (bodyEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (ctx.addRetained key shape fresh) Reference History),
      body.execute Reference state = state.mapClassical (fun entry =>
        ((step entry.1).1, (entry.2, (step entry.1).2))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.seq (.retain ctx key shape fresh) body).execute Reference state =
      state.mapClassical (fun entry =>
        ((step (entry.1.pushRetained key shape fresh)).1,
          (entry.2, ((), (step (entry.1.pushRetained key shape fresh)).2)))) := by
  simp only [execute_seq, bodyEquation, execute_retain, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Circuit
