/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Interpret.Laws
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
theorem execute_seq_retained_mapClassical_tail {kind : ProblemKind}
    {pre middle : RuntimeCtx kind} (key : StorageKey) (shape : CShape) (fresh : key ∉ middle.keys)
    (first : Circuit pre middle) (second : Circuit middle (middle.addRetained key shape fresh))
    (step : Store middle → Store (middle.addRetained key shape fresh) × second.Path)
    (secondEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State middle Reference History),
      second.execute Reference state = state.mapClassical (fun entry =>
        ((step entry.1).1, (entry.2, (step entry.1).2))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State pre Reference History) :
    (Circuit.seq first second).execute Reference state =
      (first.execute Reference state).mapClassical (fun entry =>
        ((step entry.1).1, (entry.2.1, (entry.2.2, (step entry.1).2)))) := by
  simp only [execute_seq, secondEquation, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Circuit
