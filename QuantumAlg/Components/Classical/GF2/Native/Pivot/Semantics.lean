/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Pivot
import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Materialize.Semantics
import all QuantumAlg.Components.Classical.GF2.Native.Eliminate.Semantics

/-!
# Complete records of the original ordered pivot search

Every decision reads its actual intermediate store. The increasing row scan
retains all genuine branch paths and original marker instructions; lexical
entry and exit preserve every caller-store, reference and history block.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

private theorem operation_execute {input output : CShape} (op : ClassicalOp input output ctx ctx)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.classical op).execute Reference state =
      state.mapClassical (D := Store ctx × (History × (Circuit.classical op).Path))
        (fun entry => (entry.1.applyOp op, (entry.2, ()))) := by
  refine (Circuit.execute_classical_mapClassical op Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

private theorem idle_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.id ctx).execute Reference state =
      state.mapClassical (D := Store ctx × (History × (Circuit.id ctx).Path))
        (fun entry => (entry.1, (entry.2, ()))) := by
  refine (Circuit.execute_id_mapClassical Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

variable (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
  (used : CWriteRef ctx (.unsignedWord rowCount))
  (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
  (columns : CWriteRef ctx (.unsignedWord width)) (found sink : CWriteRef ctx .bit)

/-- The selected row follows its five actual stages and their intermediate stores. -/
def selectPivotStep (pivot : Fin rowCount) (column : Fin width) (store : Store ctx) :
    Store ctx × (selectPivot matrix used rows columns found sink pivot column).Path :=
  Circuit.sequenceRecord (.classical (pivotSelectedOp sink))
      (.seq
        (.classical (pivotFoundOp found))
      (.seq (materializePivotRow used rows pivot column)
      (.seq (materializePivotColumn columns column) (eliminateWithPivot matrix pivot column))))
  (fun current => (current.applyOp (pivotSelectedOp sink), ()))
  (Circuit.sequenceRecord (.classical (pivotFoundOp found))
      (.seq (materializePivotRow used rows pivot column)
      (.seq (materializePivotColumn columns column) (eliminateWithPivot matrix pivot column)))
    (fun current => (current.applyOp (pivotFoundOp found), ()))
    (Circuit.sequenceRecord (materializePivotRow used rows pivot column)
      (.seq (materializePivotColumn columns column) (eliminateWithPivot matrix pivot column))
      (materializePivotRowStep used rows pivot column)
      (Circuit.sequenceRecord (materializePivotColumn columns column)
        (eliminateWithPivot matrix pivot column)
        (materializePivotColumnStep columns column)
        (eliminateWithPivotStep matrix pivot column)))) store

/-- The selected-pivot sequence acts on every complete store/reference/history block. -/
theorem gf2SelectPivot_execute (pivot : Fin rowCount) (column : Fin width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (selectPivot matrix used rows columns found sink pivot column).execute Reference state =
      state.mapClassical (fun entry =>
        ((selectPivotStep matrix used rows columns found sink pivot column entry.1).1,
          (entry.2, (selectPivotStep matrix used rows columns found sink pivot column entry.1).2)))
            :=
  Circuit.execute_sequenceRecord _ _ _ _ (operation_execute (pivotSelectedOp sink))
  (Circuit.execute_sequenceRecord _ _ _ _ (operation_execute (pivotFoundOp found))
    (Circuit.execute_sequenceRecord _ _ _ _ (gf2MaterializePivotRow_execute used rows pivot column)
      (Circuit.execute_sequenceRecord _ _ _ _ (gf2MaterializePivotColumn_execute columns column)
        (gf2EliminateWithPivot_execute matrix pivot column)))) Reference state

/-- The actual matrix-bit decision retains either its selected record or its rejection copy. -/
def pivotMatrixChoiceStep (row : Fin rowCount) (column : Fin width)
    (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (pivotMatrixChoice matrix used rows columns found sink row column value).Path :=
  match value with
  | .bit false => (store.applyOp (pivotRejectedOp sink), ())
  | .bit true => selectPivotStep matrix used rows columns found sink row column store

private theorem pivotMatrixChoice_execute (row : Fin rowCount) (column : Fin width)
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (pivotMatrixChoice matrix used rows columns found sink row column value).execute Reference state
      =
      state.mapClassical (fun entry =>
        ((pivotMatrixChoiceStep matrix used rows columns found sink row column value entry.1).1,
          (entry.2,
            (pivotMatrixChoiceStep matrix used rows columns found sink row column value
              entry.1).2))) :=
  by
    cases value with
    | bit bit =>
        cases bit
        · exact operation_execute (pivotRejectedOp sink) Reference state
        · exact gf2SelectPivot_execute matrix used rows columns found sink row column
            Reference state

/-- A used row is rejected directly; an unused row records the actual matrix-bit branch. -/
def pivotUsedChoiceStep (row : Fin rowCount) (column : Fin width)
    (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (pivotUsedChoice matrix used rows columns found sink row column value).Path :=
  match value with
  | .bit false =>
      let bit := store.read (eliminationBit matrix row column)
      let actual := pivotMatrixChoiceStep matrix used rows columns found sink row column bit store
      (actual.1, ⟨bit, actual.2⟩)
  | .bit true => (store.applyOp (pivotRejectedOp sink), ())

private theorem pivotUsedChoice_execute (row : Fin rowCount) (column : Fin width)
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (pivotUsedChoice matrix used rows columns found sink row column value).execute Reference state =
      state.mapClassical (fun entry =>
        ((pivotUsedChoiceStep matrix used rows columns found sink row column value entry.1).1,
          (entry.2,
            (pivotUsedChoiceStep matrix used rows columns found sink row column value entry.1).2)))
              :=
  by
    cases value with
    | bit bit =>
        cases bit
        · exact Circuit.execute_branch_mapClassical (eliminationBit matrix row column)
            (pivotMatrixChoice matrix used rows columns found sink row column)
            (pivotMatrixChoiceStep matrix used rows columns found sink row column)
            (pivotMatrixChoice_execute matrix used rows columns found sink row column) Reference
              state
        · exact operation_execute (pivotRejectedOp sink) Reference state

/-- A previously found pivot is unchanged; otherwise the actual used-bit branch is recorded. -/
def pivotFoundChoiceStep (row : Fin rowCount) (column : Fin width)
    (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (pivotFoundChoice matrix used rows columns found sink row column value).Path :=
  match value with
  | .bit false =>
      let bit := store.read (pivotUsedBit used row)
      let actual := pivotUsedChoiceStep matrix used rows columns found sink row column bit store
      (actual.1, ⟨bit, actual.2⟩)
  | .bit true => (store, ())

private theorem pivotFoundChoice_execute (row : Fin rowCount) (column : Fin width)
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (pivotFoundChoice matrix used rows columns found sink row column value).execute Reference state
      =
      state.mapClassical (fun entry =>
        ((pivotFoundChoiceStep matrix used rows columns found sink row column value entry.1).1,
          (entry.2,
            (pivotFoundChoiceStep matrix used rows columns found sink row column value entry.1).2)))
              :=
  by
    cases value with
    | bit bit =>
        cases bit
        · exact Circuit.execute_branch_mapClassical (pivotUsedBit used row)
            (pivotUsedChoice matrix used rows columns found sink row column)
            (pivotUsedChoiceStep matrix used rows columns found sink row column)
            (pivotUsedChoice_execute matrix used rows columns found sink row column) Reference state
        · exact idle_execute Reference state

/-- The actual row-probe record begins with the current found latch. -/
def pivotProbeRowStep (row : Fin rowCount) (column : Fin width) (store : Store ctx) :
    Store ctx × (pivotProbeRow matrix used rows columns found sink row column).Path :=
  let value := store.read (.storage found.toCStorageRef)
  let actual := pivotFoundChoiceStep matrix used rows columns found sink row column value store
  (actual.1, ⟨value, actual.2⟩)

/-- All three original stored-bit decisions preserve their actual complete state correlations. -/
theorem gf2PivotProbeRow_execute (row : Fin rowCount) (column : Fin width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (pivotProbeRow matrix used rows columns found sink row column).execute Reference state =
      state.mapClassical (fun entry =>
        ((pivotProbeRowStep matrix used rows columns found sink row column entry.1).1,
          (entry.2, (pivotProbeRowStep matrix used rows columns found sink row column entry.1).2)))
            :=
  Circuit.execute_branch_mapClassical (.storage found.toCStorageRef)
    (pivotFoundChoice matrix used rows columns found sink row column)
    (pivotFoundChoiceStep matrix used rows columns found sink row column)
    (pivotFoundChoice_execute matrix used rows columns found sink row column) Reference state

/-- The final no-pivot record keeps the original real self-XOR only in the unfound branch. -/
def pivotAbsentChoiceStep (sink : CWriteRef ctx .bit) (value : CShape.Value .bit)
    (store : Store ctx) : Store ctx × (pivotAbsentChoice sink value).Path :=
  match value with
  | .bit false => (store.applyOp (pivotClearOp sink), ())
  | .bit true => (store, ())

private theorem pivotAbsentChoice_execute (sink : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (pivotAbsentChoice sink value).execute Reference state =
      state.mapClassical (fun entry =>
        ((pivotAbsentChoiceStep sink value entry.1).1,
          (entry.2, (pivotAbsentChoiceStep sink value entry.1).2))) := by
  cases value with
  | bit bit =>
      cases bit
      · exact operation_execute (pivotClearOp sink) Reference state
      · exact idle_execute Reference state

/-- Clear, ordered actual row records and the original final found decision. -/
def reduceColumnBodyStep (column : Fin width) (store : Store ctx) :
    Store ctx × (reduceColumnBody matrix used rows columns found sink column).Path :=
  Circuit.sequenceRecord (.classical (pivotClearOp found))
    (.seq (Circuit.forRange rowCount
      (fun row => pivotProbeRow matrix used rows columns found sink row column))
      (.branch (.storage found.toCStorageRef) (pivotAbsentChoice sink)))
    (fun current => (current.applyOp (pivotClearOp found), ()))
    (Circuit.sequenceRecord (Circuit.forRange rowCount
      (fun row => pivotProbeRow matrix used rows columns found sink row column))
      (.branch (.storage found.toCStorageRef) (pivotAbsentChoice sink))
      (Circuit.forRangeRecord rowCount
        (fun row => pivotProbeRow matrix used rows columns found sink row column)
        (fun row => pivotProbeRowStep matrix used rows columns found sink row column))
      (fun current =>
        let value := current.read (.storage found.toCStorageRef)
        let actual := pivotAbsentChoiceStep sink value current
        (actual.1, ⟨value, actual.2⟩))) store

/-- One complete column body retains its actual increasing-order scan and all old correlations. -/
theorem gf2ReduceColumnBody_execute (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (reduceColumnBody matrix used rows columns found sink column).execute Reference state =
      state.mapClassical (fun entry =>
        ((reduceColumnBodyStep matrix used rows columns found sink column entry.1).1,
          (entry.2, (reduceColumnBodyStep matrix used rows columns found sink column entry.1).2)))
            :=
  Circuit.execute_sequenceRecord _ _ _ _ (operation_execute (pivotClearOp found))
    (Circuit.execute_sequenceRecord _ _ _ _
      (Circuit.execute_forRangeRecord rowCount _ _
        (fun row => gf2PivotProbeRow_execute matrix used rows columns found sink row column))
      (fun reference {_} _ current => Circuit.execute_branch_mapClassical
        (.storage found.toCStorageRef) (pivotAbsentChoice sink) (pivotAbsentChoiceStep sink)
        (pivotAbsentChoice_execute sink) reference current)) Reference state

/-- The first lexical exit removes only the actual found latch after the complete column body. -/
def scopedPivotSearchStep (column : Fin width) (store : Store (pivotSinkContext ctx)) :
    Store (pivotSinkContext ctx) × (scopedPivotSearch matrix used rows columns column).Path :=
  let actual := reduceColumnBodyStep (pivotSearchWrite matrix) (pivotSearchWrite used)
    (pivotSearchWrite rows) (pivotSearchWrite columns) (pivotLatch (pivotSinkContext ctx))
    ((pivotLatch ctx).underWorkspace (pivotSinkContext ctx).canonicalFreshKey .bit
      (pivotSinkContext ctx).canonicalFreshKey_fresh) column
    (store.pushWorkspace (pivotSinkContext ctx).canonicalFreshKey .bit
      (pivotSinkContext ctx).canonicalFreshKey_fresh)
  (Store.popWorkspace (pivotSinkContext ctx).canonicalFreshKey .bit
    (pivotSinkContext ctx).canonicalFreshKey_fresh actual.1, actual.2)

private theorem scopedPivotSearch_execute (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History] (state : State (pivotSinkContext ctx) Reference History) :
    (scopedPivotSearch matrix used rows columns column).execute Reference state =
      state.mapClassical (fun entry =>
        ((scopedPivotSearchStep matrix used rows columns column entry.1).1,
          (entry.2, (scopedPivotSearchStep matrix used rows columns column entry.1).2))) :=
  Circuit.execute_workspace_mapClassical _ _ _ _ _
    (gf2ReduceColumnBody_execute _ _ _ _ _ _ column) Reference state

/-- The complete real column record initializes both bits and releases found before sink. -/
def reduceColumnStep (column : Fin width) (store : Store ctx) :
    Store ctx × (reduceColumn matrix used rows columns column).Path :=
  let actual := scopedPivotSearchStep matrix used rows columns column
    (store.pushWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh actual.1, actual.2)

/-- The actual per-column circuit preserves every arbitrary caller-store/reference/history block. -/
theorem gf2ReduceColumn_execute (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (reduceColumn matrix used rows columns column).execute Reference state =
      state.mapClassical (fun entry =>
        ((reduceColumnStep matrix used rows columns column entry.1).1,
          (entry.2, (reduceColumnStep matrix used rows columns column entry.1).2))) :=
  Circuit.execute_workspace_mapClassical _ _ _ _ _
    (scopedPivotSearch_execute matrix used rows columns column) Reference state

end

end QuantumAlg.ClassicalRoutines.GF2.Native
