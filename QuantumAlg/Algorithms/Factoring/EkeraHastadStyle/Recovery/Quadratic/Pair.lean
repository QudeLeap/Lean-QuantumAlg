/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Selection

/-!
# Actual complete checks followed by the original left-priority selection

Both candidates undergo all six range and divisibility instructions, including
when an earlier result is already accepted. Only then do the two actual
first-accepted selectors consume the computed validity cells in source order.
The same structural references supply checked words to those possible copies.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Pair

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The two actual checker interfaces and the shared real first-factor latches. -/
structure Refs (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Check for the lower quadratic candidate. -/
  first : Check.Refs ctx width
  /-- Check for the upper quadratic candidate. -/
  second : Check.Refs ctx width
  /-- Persistent latches shared with preceding candidate pairs. -/
  selection : FirstAccepted.Refs ctx width

/-- The selector reads the same candidate word and actual final checker bit. -/
def selectedInputs (checked : Check.Refs ctx width) : FirstAccepted.Inputs ctx width where
  eligible := .storage checked.divisor.valid.toCStorageRef
  candidate := checked.divisor.candidate

/-- All twelve actual writes before left-priority selection. -/
def checkedStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  Check.storeStep refs.second (Check.storeStep refs.first store)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Both complete checks run before any first-factor latch is conditionally updated. -/
def code (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (Check.code (model := model) refs.first)
    (.seq (Check.code (model := model) refs.second)
      (Selection.code (model := model)
        (selectedInputs refs.first) (selectedInputs refs.second) refs.selection))

/-- The actual complete store and chronological paths of checking and selection. -/
def step (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (code (model := model) refs).Path :=
  let first := Check.step (model := model) refs.first store
  let second := Check.step (model := model) refs.second first.1
  let selected := Selection.step (model := model)
    (selectedInputs refs.first) (selectedInputs refs.second) refs.selection second.1
  (selected.1, (first.2, (second.2, selected.2)))

/-- Complete actual pair execution preserves every incoming quantum-reference block. -/
lemma nativeQuadratic_pair_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (code (model := model) refs).execute environment
      Reference state = state.mapClassical (fun entry =>
      let actual := step (model := model) refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [code, Circuit.execute_seq, Check.nativeQuadratic_check_execute,
    Selection.nativeQuadratic_selection_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Pair
