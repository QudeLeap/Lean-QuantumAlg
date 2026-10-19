/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Context.Retained.State
import all QuantumAlg.Core.Execution.Circuit.History

/-!
# Complete coordinates of all existing finite measurement cells

The original recursive cell Stores and zero-wire references stay explicit.
These coordinate definitions allow arbitrary correlations and stored values.
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
def underMeasurementCellsSplitState {Hidden : Type} [Fintype Hidden] : (count : Nat) →
    {Reference : Register} → {H : Type} → [Fintype H] →
    State (MeasurementCells.context ctx dimension count) Reference (Hidden × H) →
    State ctx (measurementCellsReference ctx dimension count Reference)
      (Hidden × (measurementCellsHistory ctx dimension count × H))
  | 0, _, _, _, state => state.mapHistory (fun history => (history.1, ((), history.2)))
  | count + 1, _, _, _, state =>
      let inner := MeasurementCells.context ctx dimension count
      (underMeasurementCellsSplitState count
        (underRetainedSplitState inner.canonicalFreshKey (.finite dimension)
          inner.canonicalFreshKey_fresh state)).mapHistory
            (fun record => (record.1, ((record.2.1, record.2.2.1), record.2.2.2)))

private lemma retainedSplit_history {inner : RuntimeCtx kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    {Reference : Register} {Hidden H K : Type} [Fintype Hidden] [Fintype H] [Fintype K]
    (state : State (inner.addRetained key shape fresh) Reference (Hidden × H)) (update : H → K) :
    underRetainedSplitState key shape fresh
        (state.mapHistory (fun record => (record.1, update record.2))) =
      (underRetainedSplitState key shape fresh state).mapHistory
        (fun record => (record.1, (record.2.1, update record.2.2))) := by
  unfold underRetainedSplitState
  rw [retainedUnionState_history, ContextUnion.contextUnion_splitServiceState_mapHistory]

/-- Splitting the real cells commutes with any change of the original history coordinates. -/
lemma underMeasurementCellsSplitState_history (count : Nat)
    {Reference : Register} {Hidden H K : Type} [Fintype Hidden] [Fintype H] [Fintype K]
    (state : State (MeasurementCells.context ctx dimension count) Reference (Hidden × H))
    (update : H → K) :
    underMeasurementCellsSplitState ctx dimension count
        (state.mapHistory (fun record => (record.1, update record.2))) =
      (underMeasurementCellsSplitState ctx dimension count state).mapHistory
        (fun record => (record.1, (record.2.1, update record.2.2))) := by
  induction count generalizing Reference H K with
  | zero =>
      simp only [underMeasurementCellsSplitState, State.mapHistory_comp, Function.comp_def]
      erw [State.mapHistory_comp]
      rfl
  | succ count ih =>
      simp only [underMeasurementCellsSplitState]
      rw [retainedSplit_history]
      erw [ih (underRetainedSplitState
        (MeasurementCells.context ctx dimension count).canonicalFreshKey (.finite dimension)
        (MeasurementCells.context ctx dimension count).canonicalFreshKey_fresh state)
        (fun record : Store (measurementCellFrame ctx dimension count) × H =>
          (record.1, update record.2))]
      repeat' erw [State.mapHistory_comp]
      rfl

end

end QuantumAlg.Circuit
