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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth candidateWidth : Nat}

/-- Only the actual true activity branch invokes a lexical candidate visit. -/
def activityChoice (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth)
    (value : CShape.Value .bit) : Circuit ctx ctx :=
  if value.toBool then activeVisit spec base cells else .id ctx

/-- The concrete selected activity update and its actual branch path. -/
def activityChoiceStep (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth)
    (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (activityChoice spec base cells value).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => activeVisitStep spec base cells store

private theorem activityChoice_execute (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth)
    (value : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (activityChoice spec base cells value).execute Reference state =
      state.mapClassical (fun entry =>
        ((activityChoiceStep spec base cells value entry.1).1,
          (entry.2, (activityChoiceStep spec base cells value entry.1).2))) := by
  cases value with
  | bit value =>
      cases value
      · refine (Circuit.execute_id_mapClassical Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _
      · exact nativeScan_activeVisit_execute spec base cells Reference state

/-- Every actual finite slot first reads the current stored activity latch. -/
def scanSlot (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) : Circuit ctx ctx :=
  .branch (cellRead cells.cursor.active) (activityChoice spec base cells)

/-- Concrete slot record, including the activity value read from its real incoming store. -/
def scanSlotStep (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) (store : Store ctx) :
    Store ctx × (scanSlot spec base cells).Path :=
  let value := store.read (cellRead cells.cursor.active)
  let selected := activityChoiceStep spec base cells value store
  (selected.1, ⟨value, selected.2⟩)

/-- The actual slot executes precisely the branch selected by its real activity read. -/
theorem nativeScan_slot_execute (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (scanSlot spec base cells).execute Reference state =
      state.mapClassical (fun entry =>
        ((scanSlotStep spec base cells entry.1).1,
          (entry.2, (scanSlotStep spec base cells entry.1).2))) :=
  Circuit.execute_branch_mapClassical (cellRead cells.cursor.active)
    (activityChoice spec base cells) (activityChoiceStep spec base cells)
    (activityChoice_execute spec base cells) Reference state

/-- The complete finite scan uses the existing circuit iteration constructor. -/
def scan (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) (fuel : Nat) : Circuit ctx ctx :=
  .iterate fuel (scanSlot spec base cells)

/-- The only interpreter's final store and every actual finite slot path are correlated. -/
theorem nativeScan_execute (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) (fuel : Nat) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (scan spec base cells fuel).execute Reference state =
      state.mapClassical (fun entry =>
        ((fun store => (scanSlotStep spec base cells store).1)^[fuel] entry.1,
          (entry.2, fun index : Fin fuel =>
            (scanSlotStep spec base cells
              ((fun store => (scanSlotStep spec base cells store).1)^[index.val] entry.1)).2))) :=
  Circuit.execute_iterate_mapClassical (scanSlot spec base cells) (scanSlotStep spec base cells)
    (nativeScan_slot_execute spec base cells) fuel Reference state

/-- An actual inactive slot leaves the entire real store unchanged. -/
theorem nativeScan_slot_inactive (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) (store : Store ctx)
    (inactive : store.read (cellRead cells.cursor.active) = .bit false) :
    (scanSlotStep spec base cells store).1 = store := by
  change (activityChoiceStep spec base cells
    (store.read (cellRead cells.cursor.active)) store).1 = store
  exact congrArg (fun value => (activityChoiceStep spec base cells value store).1) inactive

/-- The selected inactive branch contributes no synthetic arithmetic or padded event. -/
theorem nativeScan_inactive_eventTrace (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth)
    (path : (activityChoice spec base cells (.bit false)).Path) :
    (activityChoice spec base cells (.bit false)).eventTrace path = [] := rfl

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
