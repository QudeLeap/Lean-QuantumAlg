/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Prepared
import all QuantumAlg.Core.Execution.Circuit.History

/-!
# Actual native preparation with complete source-stage histories

The real first and last interpreters surround the native operator granted
to the actual preparation instruction. Omitting its unique unit path gives
an exact compressed record type. The execution identity restores that path
through the explicit history bijection; no measured outcome is discarded.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open Execution

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {Reference : Register}

namespace PreparedStage

/-- Insert the actual native unit path while retaining both original measured paths. -/
def headHistory (prepared : PreparedStage ctx operations services Reference) (History : Type) :
    ((History × prepared.stage.first.Path) × prepared.stage.last.Path) →
      History × prepared.code.Path :=
  fun value => (value.1.1, (value.1.2, ((), value.2)))

/-- The same real first/last execution, with only the native instruction's unit path compressed. -/
def runHead (prepared : PreparedStage ctx operations services Reference)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    State ctx Reference
      (services.HiddenState × ((History × prepared.stage.first.Path) ×
        prepared.stage.last.Path)) :=
  prepared.stage.last.execute environment Reference
    ((prepared.stage.first.execute environment Reference state).applyUnitary (fun _ =>
      UnitaryOperator.prodTensor (prepared.prepare.matrix environment.quantum)
        (1 : UnitaryOperator Reference)))

/-- The literal native instruction contributes precisely its unique real unit path. -/
lemma window_preparedHead_execute (prepared : PreparedStage ctx operations services Reference)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    prepared.code.execute environment Reference state =
      (prepared.runHead environment state).mapHistory (fun value =>
        (value.1, prepared.headHistory History value.2)) := by
  let nativeState : State ctx Reference
      (services.HiddenState × (History × prepared.stage.first.Path)) :=
    (prepared.stage.first.execute environment Reference state).applyUnitary (fun _ =>
      UnitaryOperator.prodTensor (prepared.prepare.matrix environment.quantum)
        (1 : UnitaryOperator Reference))
  have nativeLaw : (Circuit.unitary (operations := operations) (classicalOracles := services)
      (allowAllocation := true) prepared.prepare).execute environment Reference
        (prepared.stage.first.execute environment Reference state) =
      nativeState.mapHistory (fun value => (value.1, (value.2, ()))) :=
    (Circuit.execute_unitary environment
      (prepared.stage.first.execute environment Reference state) prepared.prepare).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  unfold code
  rw [Circuit.execute_seq, Circuit.execute_seq, nativeLaw]
  have moved := prepared.stage.last.execute_mapHistory environment Reference nativeState
    (fun history : History × prepared.stage.first.Path => (history, ()))
  refine (congrArg (fun current : State ctx Reference
      (services.HiddenState × (((History × prepared.stage.first.Path) × Unit) ×
        prepared.stage.last.Path)) =>
    (current.mapHistory (fun history =>
      (history.1, (history.2.1.1, (history.2.1.2, history.2.2))))).mapHistory
        (fun history =>
          (history.1, (history.2.1.1, (history.2.1.2, history.2.2))))) moved).trans ?_
  simp only [State.mapHistory_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Structural execution of the original prepared list, retaining both real paths at each node. -/
def run (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
    services).Environment) :
    (prepared : List (PreparedStage ctx operations services Reference)) →
      {History : Type} → [Fintype History] →
      State ctx Reference (services.HiddenState × History) →
        State ctx Reference
          (services.HiddenState × Stage.Records (prepared.map PreparedStage.stage) History)
  | [], _, _, state => state
  | head :: rest, _, _, state => run environment rest (head.runHead environment state)

/-- The actual whole sequence returns the bijective record of the same compressed execution. -/
lemma window_preparedSequence_execute
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (prepared : List (PreparedStage ctx operations services Reference))
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (sequence prepared).execute environment Reference state =
      (run environment prepared state).mapHistory (fun value =>
        (value.1, historyEquiv prepared History value.2)) := by
  induction prepared generalizing History with
  | nil =>
      change (Circuit.id (model := .quantum AlgorithmGate.model .empty operations services)
        (allowAllocation := true) ctx).execute environment Reference state = _
      rw [Circuit.execute_id]
      exact ExecutionState.executionState_mapClassical_congr _ rfl
  | cons head rest ih =>
      change (head.code.seq (sequence rest)).execute environment Reference state = _
      rw [Circuit.execute_seq, head.window_preparedHead_execute environment state]
      have moved := (sequence rest).execute_mapHistory environment Reference
        (head.runHead environment state) (head.headHistory History)
      refine (congrArg (fun current : State ctx Reference
        (services.HiddenState × ((History × head.code.Path) × (sequence rest).Path)) =>
          current.mapHistory (fun history =>
            (history.1, (history.2.1.1, (history.2.1.2, history.2.2))))) moved).trans ?_
      rw [ih]
      simp only [State.mapHistory_comp, Function.comp_def]
      exact ExecutionState.executionState_mapClassical_congr _ rfl

end PreparedStage

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
