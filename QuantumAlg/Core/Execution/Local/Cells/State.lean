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

private theorem retainedSplit_history {inner : RuntimeCtx kind}
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
theorem underMeasurementCellsSplitState_history (count : Nat)
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

/-- The complete state executes the original local code along the corresponding actual path. -/
theorem underMeasurementCells_execute {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (dimension : ℕ+)
    (code : Circuit model ctx ctx) (supported : code.IsLocal)
    (count : Nat) {Reference : Register} {H : Type} [Fintype H]
    (state : State (MeasurementCells.context ctx dimension count) Reference
      (model.HiddenState × H)) :
    underMeasurementCellsSplitState ctx dimension count
        ((underMeasurementCells code supported dimension count).execute Reference state) =
      (code.execute (measurementCellsReference ctx dimension count Reference)
        (underMeasurementCellsSplitState ctx dimension count state)).mapHistory
          (fun record => (record.1, (record.2.1.1,
            (record.2.1.2,
              underMeasurementCellsPathEquiv code supported dimension count record.2.2)))) := by
  induction count generalizing Reference H with
  | zero =>
      simp only [underMeasurementCellsSplitState, measurementCellsReference,
        underMeasurementCells, localUnderMeasurementCells, underMeasurementCellsPathEquiv]
      erw [execute_mapHistory code Reference state (fun history : H => ((), history))]
      erw [State.mapHistory_comp]
      rfl
  | succ count ih =>
      let inner := MeasurementCells.context ctx dimension count
      let prior := localUnderMeasurementCells code supported dimension count
      let split := underRetainedSplitState inner.canonicalFreshKey (.finite dimension)
        inner.canonicalFreshKey_fresh state
      let retainedPath := underRetainedPathEquiv prior.val prior.property inner.canonicalFreshKey
        (.finite dimension) inner.canonicalFreshKey_fresh
      simp only [underMeasurementCellsSplitState, measurementCellsReference,
        underMeasurementCells, localUnderMeasurementCells]
      erw [underRetained_execute inner.canonicalFreshKey (.finite dimension)
        inner.canonicalFreshKey_fresh prior.val prior.property state]
      erw [underMeasurementCellsSplitState_history ctx dimension count
        (prior.val.execute ((measurementCellFrame ctx dimension count).register.prod Reference)
          split)
        (fun record : (Store (measurementCellFrame ctx dimension count) × H) × prior.val.Path =>
          (record.1.1, (record.1.2, retainedPath record.2)))]
      erw [ih (state := split)]
      erw [execute_mapHistory code
        (measurementCellsReference ctx dimension count
          ((measurementCellFrame ctx dimension count).register.prod Reference))
        (underMeasurementCellsSplitState ctx dimension count split)
        (fun record : measurementCellsHistory ctx dimension count ×
          (Store (measurementCellFrame ctx dimension count) × H) =>
          ((record.1, record.2.1), record.2.2))]
      repeat' erw [State.mapHistory_comp]
      rfl

end

end QuantumAlg.Circuit
