/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Input.Oracle

/-!
# Borrowed restoration with an existing finite execution history

The actual interpreter ignores mathematical history labels. Equality of the
complete input after summing those labels therefore transports a whole-run
borrowed guarantee to the existing history encoding. This sums no physical
borrowed coordinate and retains the complete original quantum reference.
-/

namespace QuantumAlg

noncomputable section

attribute [local instance] Classical.decEq

open Execution

private lemma execute_borrowed_ignores_history
    {model : ExecutionModel} {ctx : RuntimeCtx model.kind} {allowAllocation : Bool}
    (code : Circuit model ctx ctx allowAllocation)
    (environment : model.Environment) (Reference : Register)
    {H K : Type} [Fintype H] [Fintype K]
    (first : State ctx Reference (model.HiddenState × H))
    (second : State ctx Reference (model.HiddenState × K))
    (same : first.mapClassical (fun record => (record.1, record.2.1)) =
      second.mapClassical (fun record => (record.1, record.2.1))) :
    observeBorrowed Reference (code.execute environment Reference first) =
      observeBorrowed Reference (code.execute environment Reference second) := by
  have initial : first.mapHistory (fun record => (record.1, ())) =
      second.mapHistory (fun record => (record.1, ())) := by
    have erased := congrArg
      (fun state : State ctx Reference model.HiddenState =>
        state.mapClassical (fun record => (record.1, (record.2, ())))) same
    simp only [ExecutionState.executionState_mapClassical_comp, Function.comp_def] at erased
    calc
      _ = first.mapClassical (fun record => (record.1, (record.2.1, ()))) :=
        ExecutionState.executionState_mapClassical_congr first rfl
      _ = second.mapClassical (fun record => (record.1, (record.2.1, ()))) := erased
      _ = _ := ExecutionState.executionState_mapClassical_congr second rfl
  have executed := congrArg (code.execute environment Reference) initial
  rw [code.execute_mapHistory environment Reference first (fun _ : H => ()),
    code.execute_mapHistory environment Reference second (fun _ : K => ())] at executed
  have observed := congrArg (observeBorrowed Reference) executed
  simpa only [observeBorrowed_mapHistory] using observed

/-- A whole-run restoration guarantee applies to every encoding of the same mathematical history. -/
lemma algorithmRun_restoresBorrowed_with_history
    {model : ExecutionModel} {ctx : RuntimeCtx model.kind} {shape : CShape}
    {allowAllocation : Bool} (run : AlgorithmRun model ctx ctx shape allowAllocation)
    (environment : model.Environment)
    {Reference : Register} (input : OracleInput model.classicalOracles ctx Reference)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (same : state.mapClassical (fun record => (record.1, record.2.1)) = input.state)
    (restores : run.RestoresBorrowed environment input) :
    run.code.BorrowedRestored Reference state (run.code.execute environment Reference state) := by
  have initial : state.mapClassical (fun record => (record.1, record.2.1)) =
      (input.state.mapClassical (fun record => (record.1, (record.2, record.1)))).mapClassical
        (fun record => (record.1, record.2.1)) := by
    rw [ExecutionState.executionState_mapClassical_comp]
    change _ = input.state.mapClassical id
    rw [ExecutionState.mapClassical_id]
    exact same
  have result := execute_borrowed_ignores_history run.code environment Reference state
    (input.state.mapClassical (fun record => (record.1, (record.2, record.1)))) initial
  have before : observeBorrowed Reference state = observeBorrowed Reference input.state := by
    have unchanged := observeBorrowed_mapHistory state Prod.fst
    change observeBorrowed Reference
      (state.mapClassical (fun record => (record.1, record.2.1))) =
        observeBorrowed Reference state at unchanged
    rw [same] at unchanged
    exact unchanged.symm
  change observeBorrowed Reference (run.execute environment Reference input.state) =
    observeBorrowed Reference input.state at restores
  change observeBorrowed Reference (run.code.execute environment Reference state) =
    observeBorrowed Reference state
  exact result.trans (restores.trans before.symm)

end

end QuantumAlg
