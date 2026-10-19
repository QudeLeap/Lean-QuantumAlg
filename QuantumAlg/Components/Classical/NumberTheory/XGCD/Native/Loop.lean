/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.ActiveStep.Guarded
import all QuantumAlg.Core.Execution.Classical.Iteration

/-!
# Actual stored-condition extended-Euclidean iteration

The existing iterate instruction composes the actual selected store record.
Each finite path entry is obtained from the store at that iteration, retaining
the complete quantum-reference state and all unchanged caller readings.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual final store and the real branch path at every finite iteration stage. -/
def iteratedActiveRecord {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (guardedActive
      (model := model) cells zero).Path)
    (count : Nat) (store : Store ctx × model.HiddenState) : (Store ctx × model.HiddenState) ×
      (Circuit.iterate count (guardedActive (model := model) cells zero)).Path :=
  ((fun before => (record before).1)^[count] store,
    fun index => (record ((fun before => (record before).1)^[index.val] store)).2)

/-- The same actual record interprets every full input density and finite history. -/
lemma xgcdNativeLoop_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (guardedActive
      (model := model) cells zero).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (guardedActive (model := model) cells zero).execute
        environment Reference state = state.mapClassical
        (fun entry =>
        let result := record (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (count : Nat) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.iterate count (guardedActive (model := model) cells zero)).execute
      environment Reference state =
      state.mapClassical (fun entry =>
        let result := iteratedActiveRecord (model := model) cells zero record count
          (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  exact (Circuit.execute_iterate_mapClassical (environment := environment)
    (guardedActive (model := model) cells zero) record equation count Reference state).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)

/-- A caller read preserved by each actual selected record survives every iteration count. -/
lemma xgcdNativeLoop_read_other {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (guardedActive
      (model := model) cells zero).Path)
    {shape : CShape} (other : CInputRef ctx shape)
    (preserved : ∀ before : Store ctx × model.HiddenState, ((record before).1.1).read other =
      before.1.read other)
    (count : Nat) (store : Store ctx × model.HiddenState) :
    ((iteratedActiveRecord (model := model) cells zero record count store).1.1).read other =
      store.1.read other := by
  change (((fun before => (record before).1)^[count]) store).1.read other = _
  induction count generalizing store with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [Function.iterate_succ_apply]
      exact (inductionHypothesis (record store).1).trans (preserved store)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
