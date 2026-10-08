/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Selection.Candidate.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Check.Program
import all QuantumAlg.Components.Classical.FirstAccepted.Semantics

/-!
# Actual proper-divisor check followed by canonical first-accepted selection
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidateSelect

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {shortWidth : Nat}

/-- Execute the complete check and then the canonical selector on its actual stored result. -/
def into (refs : Refs ctx shortWidth) : Circuit model ctx ctx :=
  .seq (QuadraticCandidateCheck.into refs.check)
    (FirstAccepted.circuit (selectionInputs refs) refs.selection)

/-- Actual full store and both chronological circuit paths of one checked selection. -/
def step (refs : Refs ctx shortWidth) (store : Store ctx) : Store ctx × (into refs).Path :=
  let checked := QuadraticCandidateCheck.step refs.check store
  let selected := FirstAccepted.step (selectionInputs refs) refs.selection checked.1
  (selected.1, (checked.2, selected.2))

/-- One checked selection executes its complete record on every history and external reference. -/
theorem into_execute (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := step refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [into, step, Circuit.execute_seq, QuadraticCandidateCheck.into_execute,
    FirstAccepted.firstAccepted_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidateSelect
