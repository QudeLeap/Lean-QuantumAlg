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

variable {model : ExecutionModel} [BitWord.Selected model]
  {environment : model.Environment}
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

private lemma operation_execute {input output : CShape} (op : ClassicalOp input output ctx ctx)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (BitWord.instruction (execution := model) op).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := BitWord.instructionStep (execution := model) op entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  BitWord.bitWord_instruction_execute (environment := environment) (execution := model) op state

omit [BitWord.Selected model] in
private lemma idle_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.id (allowAllocation := true) (model := model) ctx).execute environment Reference state
      =
      state.mapClassical (fun entry => (entry.1, (entry.2.1, (entry.2.2, ())))) := by
  exact (Circuit.execute_id_mapClassical (environment := environment) (allowAllocation := true)
    (model := model) Reference state).trans
    (ExecutionState.executionState_mapClassical_congr _ rfl)

variable (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
  (used : CWriteRef ctx (.unsignedWord rowCount))
  (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
  (columns : CWriteRef ctx (.unsignedWord width)) (found sink : CWriteRef ctx .bit)

/-- The selected row follows its five actual stages and their intermediate stores. -/
def selectPivotStep (pivot : Fin rowCount) (column : Fin width) (store : Store ctx) :
    Store ctx × (selectPivot matrix used rows columns found sink pivot column).Path :=
  Circuit.sequenceStoreRecord
    (BitWord.instruction (execution := model) (pivotSelectedOp sink))
      (.seq
        (BitWord.instruction (execution := model) (pivotFoundOp found))
      (.seq (materializePivotRow (model := model) used rows pivot column)
      (.seq (materializePivotColumn (model := model) columns column)
        (eliminateWithPivot (model := model) matrix pivot column))))
  (BitWord.instructionStep (execution := model) (pivotSelectedOp sink))
  (Circuit.sequenceStoreRecord
    (BitWord.instruction (execution := model) (pivotFoundOp found))
      (.seq (materializePivotRow (model := model) used rows pivot column)
      (.seq (materializePivotColumn (model := model) columns column)
        (eliminateWithPivot (model := model) matrix pivot column)))
    (BitWord.instructionStep (execution := model) (pivotFoundOp found))
    (Circuit.sequenceStoreRecord (materializePivotRow (model := model) used rows pivot column)
      (.seq (materializePivotColumn (model := model) columns column)
        (eliminateWithPivot (model := model) matrix pivot column))
      (materializePivotRowStep used rows pivot column)
      (Circuit.sequenceStoreRecord (materializePivotColumn (model := model) columns column)
        (eliminateWithPivot (model := model) matrix pivot column)
        (materializePivotColumnStep columns column)
        (eliminateWithPivotStep matrix pivot column)))) store

/-- The selected-pivot sequence acts on every complete store/reference/history block. -/
lemma gf2SelectPivot_execute (pivot : Fin rowCount) (column : Fin width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (selectPivot (model := model) matrix used rows columns found sink pivot column).execute
      environment
        Reference state =
      state.mapClassical (fun entry =>
        ((selectPivotStep matrix used rows columns found sink pivot column entry.1).1,
          (entry.2.1, (entry.2.2,
            (selectPivotStep matrix used rows columns found sink pivot column entry.1).2))))
            :=
  Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
    (operation_execute (pivotSelectedOp sink))
  (Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
    (operation_execute (pivotFoundOp found))
    (Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
      (gf2MaterializePivotRow_execute (model := model) used rows pivot column)
      (Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
        (gf2MaterializePivotColumn_execute (model := model) columns column)
        (gf2EliminateWithPivot_execute (model := model) matrix pivot column)))) Reference state

/-- The actual matrix-bit decision retains either its selected record or its rejection copy. -/
def pivotMatrixChoiceStep (row : Fin rowCount) (column : Fin width)
    (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (pivotMatrixChoice matrix used rows columns found sink row column value).Path :=
  match value with
  | .bit false => BitWord.instructionStep (execution := model) (pivotRejectedOp sink) store
  | .bit true => selectPivotStep matrix used rows columns found sink row column store

private lemma pivotMatrixChoice_execute (row : Fin rowCount) (column : Fin width)
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pivotMatrixChoice (model := model)
      matrix used rows columns found sink row column value).execute environment Reference state
      =
      state.mapClassical (fun entry =>
        ((pivotMatrixChoiceStep matrix used rows columns found sink row column value entry.1).1,
          (entry.2.1, (entry.2.2,
            (pivotMatrixChoiceStep matrix used rows columns found sink row column value
              entry.1).2)))) :=
  by
    cases value with
    | bit bit =>
        cases bit
        · exact operation_execute (pivotRejectedOp sink) Reference state
        · exact gf2SelectPivot_execute (model := model)
            matrix used rows columns found sink row column Reference state

/-- A used row is rejected directly; an unused row records the actual matrix-bit branch. -/
def pivotUsedChoiceStep (row : Fin rowCount) (column : Fin width)
    (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (pivotUsedChoice matrix used rows columns found sink row column value).Path :=
  match value with
  | .bit false =>
      let bit := store.read (eliminationBit matrix row column)
      let actual := pivotMatrixChoiceStep matrix used rows columns found sink row column bit store
      (actual.1, ⟨bit, actual.2⟩)
  | .bit true => BitWord.instructionStep (execution := model) (pivotRejectedOp sink) store

private lemma pivotUsedChoice_execute (row : Fin rowCount) (column : Fin width)
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pivotUsedChoice (model := model) matrix used rows columns found sink row column
      value).execute environment
        Reference state =
      state.mapClassical (fun entry =>
        ((pivotUsedChoiceStep matrix used rows columns found sink row column value entry.1).1,
          (entry.2.1, (entry.2.2,
            (pivotUsedChoiceStep matrix used rows columns found sink row column value entry.1).2))))
              :=
  by
    cases value with
    | bit bit =>
        cases bit
        · exact Circuit.execute_branchStoreRecord (environment := environment) (model := model)
            (eliminationBit matrix row column)
            (pivotMatrixChoice (model := model) matrix used rows columns found sink row column)
            (pivotMatrixChoiceStep matrix used rows columns found sink row column)
            (pivotMatrixChoice_execute (model := model)
              matrix used rows columns found sink row column) Reference
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

private lemma pivotFoundChoice_execute (row : Fin rowCount) (column : Fin width)
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pivotFoundChoice (model := model)
      matrix used rows columns found sink row column value).execute environment Reference state
      =
      state.mapClassical (fun entry =>
        ((pivotFoundChoiceStep matrix used rows columns found sink row column value entry.1).1,
          (entry.2.1, (entry.2.2,
            (pivotFoundChoiceStep matrix used rows columns found sink row column value
              entry.1).2))))
              :=
  by
    cases value with
    | bit bit =>
        cases bit
        · exact Circuit.execute_branchStoreRecord
            (environment := environment) (model := model) (pivotUsedBit used row)
            (pivotUsedChoice (model := model) matrix used rows columns found sink row column)
            (pivotUsedChoiceStep matrix used rows columns found sink row column)
            (pivotUsedChoice_execute (model := model)
              matrix used rows columns found sink row column) Reference state
        · refine (idle_execute (model := model) Reference state).trans ?_
          exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual row-probe record begins with the current found latch. -/
def pivotProbeRowStep (row : Fin rowCount) (column : Fin width) (store : Store ctx) :
    Store ctx × (pivotProbeRow matrix used rows columns found sink row column).Path :=
  let value := store.read (.storage found.toCStorageRef)
  let actual := pivotFoundChoiceStep matrix used rows columns found sink row column value store
  (actual.1, ⟨value, actual.2⟩)

/-- All three original stored-bit decisions preserve their actual complete state correlations. -/
lemma gf2PivotProbeRow_execute (row : Fin rowCount) (column : Fin width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pivotProbeRow (model := model) matrix used rows columns found sink row column).execute
      environment
        Reference state =
      state.mapClassical (fun entry =>
        ((pivotProbeRowStep matrix used rows columns found sink row column entry.1).1,
          (entry.2.1, (entry.2.2,
            (pivotProbeRowStep matrix used rows columns found sink row column entry.1).2))))
            :=
  Circuit.execute_branchStoreRecord
    (environment := environment) (model := model) (.storage found.toCStorageRef)
    (pivotFoundChoice (model := model) matrix used rows columns found sink row column)
    (pivotFoundChoiceStep matrix used rows columns found sink row column)
    (pivotFoundChoice_execute (model := model) matrix used rows columns found sink row column)
    Reference state

/-- The final no-pivot record keeps the original real self-XOR only in the unfound branch. -/
def pivotAbsentChoiceStep (sink : CWriteRef ctx .bit) (value : CShape.Value .bit)
    (store : Store ctx) : Store ctx × (pivotAbsentChoice sink value).Path :=
  match value with
  | .bit false => BitWord.instructionStep (execution := model) (pivotClearOp sink) store
  | .bit true => (store, ())

private lemma pivotAbsentChoice_execute (sink : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pivotAbsentChoice (model := model) sink value).execute environment Reference state =
      state.mapClassical (fun entry =>
        ((pivotAbsentChoiceStep sink value entry.1).1,
          (entry.2.1, (entry.2.2, (pivotAbsentChoiceStep sink value entry.1).2)))) := by
  cases value with
  | bit bit =>
      cases bit
      · exact operation_execute (pivotClearOp sink) Reference state
      · refine (idle_execute (model := model) Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Clear, ordered actual row records and the original final found decision. -/
def reduceColumnBodyStep (column : Fin width) (store : Store ctx) :
    Store ctx × (reduceColumnBody matrix used rows columns found sink column).Path :=
  Circuit.sequenceStoreRecord
    (BitWord.instruction (execution := model) (pivotClearOp found))
    (.seq (Circuit.forRange rowCount
      (fun row => pivotProbeRow (model := model)
        matrix used rows columns found sink row column))
      (.branch (.storage found.toCStorageRef) (pivotAbsentChoice (model := model) sink)))
    (BitWord.instructionStep (execution := model) (pivotClearOp found))
    (Circuit.sequenceStoreRecord (Circuit.forRange rowCount
      (fun row => pivotProbeRow (model := model)
        matrix used rows columns found sink row column))
      (.branch (.storage found.toCStorageRef) (pivotAbsentChoice (model := model) sink))
      (Circuit.forRangeStoreRecord rowCount
        (fun row => pivotProbeRow (model := model)
          matrix used rows columns found sink row column)
        (fun row => pivotProbeRowStep matrix used rows columns found sink row column))
      (fun current =>
        let value := current.read (.storage found.toCStorageRef)
        let actual := pivotAbsentChoiceStep sink value current
        (actual.1, ⟨value, actual.2⟩))) store

/-- One complete column body retains its actual increasing-order scan and all old correlations. -/
lemma gf2ReduceColumnBody_execute (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (reduceColumnBody (model := model) matrix used rows columns found sink column).execute
      environment
        Reference state =
      state.mapClassical (fun entry =>
        ((reduceColumnBodyStep matrix used rows columns found sink column entry.1).1,
          (entry.2.1, (entry.2.2,
            (reduceColumnBodyStep matrix used rows columns found sink column entry.1).2))))
            :=
  Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
    (operation_execute (pivotClearOp found))
    (Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
      (Circuit.execute_forRangeStoreRecord
        (environment := environment) (model := model) rowCount _ _
        (fun row => gf2PivotProbeRow_execute (model := model)
          matrix used rows columns found sink row column))
      (fun reference {_} _ current => Circuit.execute_branchStoreRecord
        (environment := environment) (model := model)
        (.storage found.toCStorageRef) (pivotAbsentChoice (model := model) sink)
        (pivotAbsentChoiceStep sink)
        (pivotAbsentChoice_execute (model := model) sink) reference current)) Reference state

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

private lemma scopedPivotSearch_execute (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (pivotSinkContext ctx) Reference (model.HiddenState × History)) :
    (scopedPivotSearch (model := model) matrix used rows columns column).execute environment
      Reference state =
      state.mapClassical (fun entry =>
        ((scopedPivotSearchStep matrix used rows columns column entry.1).1,
          (entry.2.1, (entry.2.2,
            (scopedPivotSearchStep matrix used rows columns column entry.1).2)))) :=
  Circuit.execute_workspaceStoreRecord (environment := environment) (model := model) _ _ _ _ _
    (gf2ReduceColumnBody_execute (model := model) _ _ _ _ _ _ column) Reference state

/-- The complete real column record initializes both bits and releases found before sink. -/
def reduceColumnStep (column : Fin width) (store : Store ctx) :
    Store ctx × (reduceColumn matrix used rows columns column).Path :=
  let actual := scopedPivotSearchStep matrix used rows columns column
    (store.pushWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh actual.1, actual.2)

/-- The actual per-column circuit preserves every arbitrary caller-store/reference/history block. -/
lemma gf2ReduceColumn_execute (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (reduceColumn (model := model) matrix used rows columns column).execute environment
      Reference state =
      state.mapClassical (fun entry =>
        ((reduceColumnStep matrix used rows columns column entry.1).1,
          (entry.2.1, (entry.2.2,
            (reduceColumnStep matrix used rows columns column entry.1).2)))) :=
  Circuit.execute_workspaceStoreRecord (environment := environment) (model := model) _ _ _ _ _
    (scopedPivotSearch_execute (model := model) matrix used rows columns column) Reference state

end

end QuantumAlg.ClassicalRoutines.GF2.Native
