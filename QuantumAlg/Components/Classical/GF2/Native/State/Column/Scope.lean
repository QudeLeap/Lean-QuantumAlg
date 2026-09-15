/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.State.Column
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Freshness

/-!
# Original column values through both actual pivot-search scopes

Both temporary bits are genuinely initialized and popped by the existing
column circuit. The four original mathematical fields are the same seven
allocated cells lifted through these scopes; every value equation follows
from their actual store reads. No initial-zero or caller-alias promise is used.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution ClassicalWorkspace

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

private theorem lifted_fields (cells : Cells ctx (stateShapes rowCount width))
    (key : StorageKey) (extra : CShape) (fresh : key ∉ ctx.keys) :
    ((cells.underWorkspace key extra fresh).tail.tail.tail.tail.tail.head.ref =
      cells.tail.tail.tail.tail.tail.head.ref.underWorkspace key extra fresh) ∧
    ((cells.underWorkspace key extra fresh).tail.tail.tail.tail.head.ref =
      cells.tail.tail.tail.tail.head.ref.underWorkspace key extra fresh) ∧
    ((cells.underWorkspace key extra fresh).tail.tail.tail.tail.tail.tail.head.ref =
      cells.tail.tail.tail.tail.tail.tail.head.ref.underWorkspace key extra fresh) ∧
    ((cells.underWorkspace key extra fresh).tail.tail.tail.head.ref =
      cells.tail.tail.tail.head.ref.underWorkspace key extra fresh) := by
  cases cells with
  | cons success tail0 =>
    cases tail0 with
    | cons zero tail1 =>
      cases tail1 with
      | cons candidate tail2 =>
        cases tail2 with
        | cons columns tail3 =>
          cases tail3 with
          | cons used tail4 =>
            cases tail4 with
            | cons matrix tail5 =>
              cases tail5 with
              | cons rows tail6 =>
                exact ⟨rfl, rfl, rfl, rfl⟩

private theorem push_read (store : Store ctx) (key : StorageKey) (extra : CShape)
    (fresh : key ∉ ctx.keys) {shape : CShape} (output : CWriteRef ctx shape) :
    (store.pushWorkspace key extra fresh).read
      (.storage (output.underWorkspace key extra fresh).toCStorageRef) =
        store.read (.storage output.toCStorageRef) :=
  Store.read_pushWorkspace_underWorkspace store key extra fresh (.storage output.toCStorageRef)

private theorem pop_read (key : StorageKey) (extra : CShape) (fresh : key ∉ ctx.keys)
    (store : Store (ctx.addWorkspace key extra fresh)) {shape : CShape}
    (output : CWriteRef ctx shape) :
    (Store.popWorkspace key extra fresh store).read (.storage output.toCStorageRef) =
      store.read (.storage (output.underWorkspace key extra fresh).toCStorageRef) :=
  Store.read_popWorkspace_underWorkspace key extra fresh store (.storage output.toCStorageRef)

private theorem push_values (cells : Cells ctx (stateShapes rowCount width))
    (key : StorageKey) (extra : CShape) (fresh : key ∉ ctx.keys) (store : Store ctx)
    (state : ClassicalAlgorithms.GF2.State rowCount width)
    (represented : columnStateValues cells store state) :
    columnStateValues (cells.underWorkspace key extra fresh)
      (store.pushWorkspace key extra fresh) state := by
  obtain ⟨matrix, used, rows, columns⟩ := lifted_fields cells key extra fresh
  simpa only [columnStateValues, matrix, used, rows, columns, push_read] using represented

private theorem pop_values (cells : Cells ctx (stateShapes rowCount width))
    (key : StorageKey) (extra : CShape) (fresh : key ∉ ctx.keys)
    (store : Store (ctx.addWorkspace key extra fresh))
    (state : ClassicalAlgorithms.GF2.State rowCount width)
    (represented : columnStateValues (cells.underWorkspace key extra fresh) store state) :
    columnStateValues cells (Store.popWorkspace key extra fresh store) state := by
  obtain ⟨matrix, used, rows, columns⟩ := lifted_fields cells key extra fresh
  simpa only [columnStateValues, matrix, used, rows, columns, pop_read] using represented

/-- The complete actual column circuit realizes the original pure step through both bit scopes. -/
theorem gf2ReduceColumn_cellState
    (cells : Cells ctx (stateShapes rowCount width)) (distinct : cells.Distinct)
    (column : Fin width) (store : Store ctx)
    (state : ClassicalAlgorithms.GF2.State rowCount width)
    (represented : columnStateValues cells store state)
    (absent : state.pivots.find? (fun entry => decide (entry.column = column)) = none) :
    columnStateValues cells
      (reduceColumnStep cells.tail.tail.tail.tail.tail.head.ref
        cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref
        cells.tail.tail.tail.head.ref column store).1
      (ClassicalAlgorithms.GF2.stepColumn column state) := by
  let first := cells.underWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
  let both := first.underWorkspace (pivotSinkContext ctx).canonicalFreshKey .bit
    (pivotSinkContext ctx).canonicalFreshKey_fresh
  let entered := (store.pushWorkspace ctx.canonicalFreshKey .bit
    ctx.canonicalFreshKey_fresh).pushWorkspace (pivotSinkContext ctx).canonicalFreshKey .bit
      (pivotSinkContext ctx).canonicalFreshKey_fresh
  have firstValues := push_values cells ctx.canonicalFreshKey .bit
    ctx.canonicalFreshKey_fresh store state represented
  have bothValues := push_values first (pivotSinkContext ctx).canonicalFreshKey .bit
    (pivotSinkContext ctx).canonicalFreshKey_fresh _ state firstValues
  have firstDistinct := Cells.workspaceCells_underWorkspace_distinct cells distinct
    ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
  have bothDistinct := Cells.workspaceCells_underWorkspace_distinct first firstDistinct
    (pivotSinkContext ctx).canonicalFreshKey .bit (pivotSinkContext ctx).canonicalFreshKey_fresh
  let actual := reduceColumnBodyStep
    (pivotSearchWrite cells.tail.tail.tail.tail.tail.head.ref)
    (pivotSearchWrite cells.tail.tail.tail.tail.head.ref)
    (pivotSearchWrite cells.tail.tail.tail.tail.tail.tail.head.ref)
    (pivotSearchWrite cells.tail.tail.tail.head.ref) (pivotLatch (pivotSinkContext ctx))
    ((pivotLatch ctx).underWorkspace (pivotSinkContext ctx).canonicalFreshKey .bit
      (pivotSinkContext ctx).canonicalFreshKey_fresh) column entered
  have body := gf2ReduceColumnBody_cellState both bothDistinct
    (pivotLatch (pivotSinkContext ctx))
    ((pivotLatch ctx).underWorkspace (pivotSinkContext ctx).canonicalFreshKey .bit
      (pivotSinkContext ctx).canonicalFreshKey_fresh) column entered state bothValues absent
  have firstFields := lifted_fields cells ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
  have bothFields := lifted_fields first (pivotSinkContext ctx).canonicalFreshKey .bit
    (pivotSinkContext ctx).canonicalFreshKey_fresh
  have matrixPlacement : both.tail.tail.tail.tail.tail.head.ref =
      pivotSearchWrite cells.tail.tail.tail.tail.tail.head.ref :=
    bothFields.1.trans (congrArg (fun output => output.underWorkspace
      (pivotSinkContext ctx).canonicalFreshKey .bit
      (pivotSinkContext ctx).canonicalFreshKey_fresh) firstFields.1)
  have usedPlacement : both.tail.tail.tail.tail.head.ref =
      pivotSearchWrite cells.tail.tail.tail.tail.head.ref :=
    bothFields.2.1.trans (congrArg (fun output => output.underWorkspace
      (pivotSinkContext ctx).canonicalFreshKey .bit
      (pivotSinkContext ctx).canonicalFreshKey_fresh) firstFields.2.1)
  have rowsPlacement : both.tail.tail.tail.tail.tail.tail.head.ref =
      pivotSearchWrite cells.tail.tail.tail.tail.tail.tail.head.ref :=
    bothFields.2.2.1.trans (congrArg (fun output => output.underWorkspace
      (pivotSinkContext ctx).canonicalFreshKey .bit
      (pivotSinkContext ctx).canonicalFreshKey_fresh) firstFields.2.2.1)
  have columnsPlacement : both.tail.tail.tail.head.ref =
      pivotSearchWrite cells.tail.tail.tail.head.ref :=
    bothFields.2.2.2.trans (congrArg (fun output => output.underWorkspace
      (pivotSinkContext ctx).canonicalFreshKey .bit
      (pivotSinkContext ctx).canonicalFreshKey_fresh) firstFields.2.2.2)
  rw [matrixPlacement, usedPlacement, rowsPlacement, columnsPlacement] at body
  have bodyValues : columnStateValues both actual.1
      (ClassicalAlgorithms.GF2.stepColumn column state) := body
  have foundPopped := pop_values first (pivotSinkContext ctx).canonicalFreshKey .bit
    (pivotSinkContext ctx).canonicalFreshKey_fresh actual.1 _ bodyValues
  exact pop_values cells ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh _ _ foundPopped

end

end QuantumAlg.ClassicalRoutines.GF2.Native
