/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Local.Cells
import all QuantumAlg.Core.Execution.Local.Retained.State
import all QuantumAlg.Core.Execution.Circuit.History

/-!
# Full actual state beside existing finite cells

Successive exact coordinate splittings retain every existing cell Store and
the complete external reference. These are mathematical coordinates of the
same state, without another allocation, measurement or execution rule.
Arbitrary stored values and correlations are allowed, including zero cells.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} (ctx : RuntimeCtx kind) (dimension : ℕ+)

private def measurementCellFrame (count : Nat) : RuntimeCtx kind :=
  retainedLocalFrame (MeasurementCells.context ctx dimension count).canonicalFreshKey
    (.finite dimension)

/-- The complete actual Stores of all existing cells, in their allocation order. -/
def measurementCellsHistory : Nat → Type
  | 0 => Unit
  | count + 1 => measurementCellsHistory count × Store (measurementCellFrame ctx dimension count)

/-- The existing finite Stores remain a finite history carrier. -/
noncomputable instance measurementCellsHistoryFintype (count : Nat) :
    Fintype (measurementCellsHistory ctx dimension count) := by
  induction count with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ count ih =>
      let := ih
      exact inferInstanceAs
        (Fintype (measurementCellsHistory ctx dimension count ×
          Store (measurementCellFrame ctx dimension count)))

/-- The reference coordinates retain the zero-wire register of each actual classical cell. -/
def measurementCellsReference : Nat → Register → Register
  | 0, reference => reference
  | count + 1, reference =>
      measurementCellsReference count
        ((measurementCellFrame ctx dimension count).register.prod reference)

/-- Split all existing cells while preserving their complete Stores and arbitrary joint state. -/
def underMeasurementCellsSplitState : (count : Nat) →
    {Reference : Register} → {H : Type} → [Fintype H] →
    State (MeasurementCells.context ctx dimension count) Reference H →
    State ctx (measurementCellsReference ctx dimension count Reference)
      (measurementCellsHistory ctx dimension count × H)
  | 0, _, _, _, state => state.mapHistory (fun history => ((), history))
  | count + 1, _, _, _, state =>
      let inner := MeasurementCells.context ctx dimension count
      (underMeasurementCellsSplitState count
        (underRetainedSplitState inner.canonicalFreshKey (.finite dimension)
          inner.canonicalFreshKey_fresh state)).mapHistory
            (fun record => ((record.1, record.2.1), record.2.2))

private theorem retainedSplit_history {inner : RuntimeCtx kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    {Reference : Register} {H K : Type} [Fintype H] [Fintype K]
    (state : State (inner.addRetained key shape fresh) Reference H) (update : H → K) :
    underRetainedSplitState key shape fresh (state.mapHistory update) =
      (underRetainedSplitState key shape fresh state).mapHistory
        (fun record => (record.1, update record.2)) := by
  unfold underRetainedSplitState
  rw [retainedUnionState_history, ContextUnion.contextUnion_splitState_mapHistory]

/-- Splitting the real cells commutes with any change of the original history coordinates. -/
theorem underMeasurementCellsSplitState_history (count : Nat)
    {Reference : Register} {H K : Type} [Fintype H] [Fintype K]
    (state : State (MeasurementCells.context ctx dimension count) Reference H) (update : H → K) :
    underMeasurementCellsSplitState ctx dimension count (state.mapHistory update) =
      (underMeasurementCellsSplitState ctx dimension count state).mapHistory
        (fun record => (record.1, update record.2)) := by
  induction count generalizing Reference H K with
  | zero =>
      simp only [underMeasurementCellsSplitState, State.mapHistory_comp, Function.comp_def]
      erw [State.mapHistory_comp]
      rfl
  | succ count ih =>
      simp only [underMeasurementCellsSplitState]
      rw [retainedSplit_history, ih]
      simp only [State.mapHistory_comp, Function.comp_def]
      erw [State.mapHistory_comp]
      rfl

/-- The complete state executes the original local code along the corresponding actual path. -/
theorem underMeasurementCells_execute (code : Circuit ctx ctx) (supported : code.IsLocal)
    (count : Nat) {Reference : Register} {H : Type} [Fintype H]
    (state : State (MeasurementCells.context ctx dimension count) Reference H) :
    underMeasurementCellsSplitState ctx dimension count
        ((underMeasurementCells code supported dimension count).execute Reference state) =
      (code.execute (measurementCellsReference ctx dimension count Reference)
        (underMeasurementCellsSplitState ctx dimension count state)).mapHistory
          (fun record => (record.1.1,
            (record.1.2,
              underMeasurementCellsPathEquiv code supported dimension count record.2))) := by
  induction count generalizing Reference H with
  | zero =>
      simp only [underMeasurementCellsSplitState, measurementCellsReference,
        underMeasurementCells, localUnderMeasurementCells, underMeasurementCellsPathEquiv,
        execute_mapHistory]
      erw [State.mapHistory_comp]
      rfl
  | succ count ih =>
      simp only [underMeasurementCellsSplitState, measurementCellsReference,
        underMeasurementCells, localUnderMeasurementCells]
      erw [underRetained_execute, underMeasurementCellsSplitState_history, ih,
        execute_mapHistory]
      erw [State.mapHistory_comp, State.mapHistory_comp, State.mapHistory_comp]
      rfl

end

end QuantumAlg.Circuit
