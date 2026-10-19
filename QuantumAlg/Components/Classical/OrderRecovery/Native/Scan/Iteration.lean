/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Scan.Placement
import all QuantumAlg.Core.Execution.Classical.Iteration

/-!
# Actual activity-gated finite recovery scan

Each finite slot reads the current stored active bit. Inactive slots execute
identity, with no division, validation or padded events. Active slots execute
the real lexical candidate visit and update that same active latch. Ordinary
iteration of the already-proved concrete store update describes the sole
interpreter's output; it is not an extra execution parameter.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {modulusWidth candidateWidth : Nat}

/-- Only the actual true activity branch invokes a lexical candidate visit. -/
def activityChoice (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth)
    (value : CShape.Value .bit) : Circuit model ctx ctx :=
  if value.toBool then activeVisit (model := model) spec base cells else .id ctx

/-- The concrete selected activity update and its actual branch path. -/
def activityChoiceStep (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth)
    (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (activityChoice (model := model) spec base cells value).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => activeVisitStep (model := model) spec base cells store

private lemma activityChoice_execute (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth)
    (value : CShape.Value .bit) {environment : model.Environment}
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (activityChoice (model := model) spec base cells value).execute environment Reference state =
      state.mapClassical (fun entry =>
        ((activityChoiceStep (model := model) spec base cells value entry.1).1,
          (entry.2.1, (entry.2.2,
            (activityChoiceStep (model := model) spec base cells value entry.1).2)))) := by
  cases value with
  | bit value =>
      cases value
      · refine (Circuit.execute_id_mapClassical
          (environment := environment) Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _
      · exact nativeScan_activeVisit_execute spec base cells Reference state

/-- Every actual finite slot first reads the current stored activity latch. -/
def scanSlot (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) : Circuit model ctx ctx :=
  .branch (cellRead cells.cursor.active) (activityChoice (model := model) spec base cells)

/-- Concrete slot record, including the activity value read from its real incoming store. -/
def scanSlotStep (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) (store : Store ctx) :
    Store ctx × (scanSlot (model := model) spec base cells).Path :=
  let value := store.read (cellRead cells.cursor.active)
  let selected := activityChoiceStep (model := model) spec base cells value store
  (selected.1, ⟨value, selected.2⟩)

/-- The actual slot executes precisely the branch selected by its real activity read. -/
lemma nativeScan_slot_execute (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) {environment : model.Environment}
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (scanSlot (model := model) spec base cells).execute environment Reference state =
      state.mapClassical (fun entry =>
        ((scanSlotStep (model := model) spec base cells entry.1).1,
          (entry.2.1, (entry.2.2, (scanSlotStep (model := model) spec base cells entry.1).2)))) :=
  Circuit.execute_branch_mapClassical (environment := environment) (cellRead cells.cursor.active)
    (activityChoice (model := model) spec base cells)
    (fun value entry =>
      let next := activityChoiceStep (model := model) spec base cells value entry.1
      ((next.1, entry.2), next.2))
    (fun value => activityChoice_execute spec base cells value
      (environment := environment)) Reference state

/-- The complete finite scan uses the existing circuit iteration constructor. -/
def scan (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) (fuel : Nat) : Circuit model ctx ctx :=
  .iterate fuel (scanSlot (model := model) spec base cells)

/-- The only interpreter's final store and every actual finite slot path are correlated. -/
lemma nativeScan_execute (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) (fuel : Nat)
    {environment : model.Environment}
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (scan (model := model) spec base cells fuel).execute environment Reference state =
      state.mapClassical (fun entry =>
        ((fun store => (scanSlotStep (model := model) spec base cells store).1)^[fuel] entry.1,
          (entry.2.1, (entry.2.2, fun index : Fin fuel =>
            (scanSlotStep (model := model) spec base cells
              ((fun store => (scanSlotStep (model := model) spec base cells store).1)^[index.val]
                entry.1)).2)))) := by
  let jointStep := fun before : Store ctx × model.HiddenState =>
    let actual := scanSlotStep (model := model) spec base cells before.1
    ((actual.1, before.2), actual.2)
  have iterateJoint (steps : Nat) (store : Store ctx) (hidden : model.HiddenState) :
      (fun before => (jointStep before).1)^[steps] (store, hidden) =
        ((fun current => (scanSlotStep (model := model) spec base cells current).1)^[steps] store,
          hidden) := by
    induction steps with
    | zero => rfl
    | succ steps ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
  refine (Circuit.execute_iterate_mapClassical
    (environment := environment) (scanSlot (model := model) spec base cells)
    jointStep (fun reference _history _ current => nativeScan_slot_execute spec base cells
      reference current) fuel Reference state).trans ?_
  apply ExecutionState.executionState_mapClassical_congr
  funext entry
  simp only [iterateJoint, jointStep]

/-- An actual inactive slot leaves the entire real store unchanged. -/
lemma nativeScan_slot_inactive (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) (store : Store ctx)
    (inactive : store.read (cellRead cells.cursor.active) = .bit false) :
    (scanSlotStep (model := model) spec base cells store).1 = store := by
  change (activityChoiceStep (model := model) spec base cells
    (store.read (cellRead cells.cursor.active)) store).1 = store
  exact congrArg
    (fun value => (activityChoiceStep (model := model) spec base cells value store).1) inactive

/-- The selected inactive branch contributes no synthetic arithmetic or padded event. -/
lemma nativeScan_inactive_eventTrace (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth)
    (path : (activityChoice (model := model) spec base cells (.bit false)).Path) :
    (activityChoice (model := model) spec base cells (.bit false)).eventTrace path = [] := rfl

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
