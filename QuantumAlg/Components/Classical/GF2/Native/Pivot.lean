/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Materialize
import all QuantumAlg.Components.Classical.GF2.Native.Eliminate

/-!
# Actual ordered GF(2) pivot search

Each column clears its real found latch and probes rows in increasing order.
A found pivot suppresses all later probes. Rejected, selected and absent
pivots retain their distinct original native marker instructions. Two bit
scopes enclose the search; selected row and column masks have separate lives.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

/-- The original real copy operation for a rejected row probe. -/
def pivotRejectedOp (sink : CWriteRef ctx .bit) : ClassicalOp .bit .bit ctx ctx :=
  .bit .copy ctx (.storage sink.toCStorageRef) sink

/-- The original real self-AND operation for the selected row probe. -/
def pivotSelectedOp (sink : CWriteRef ctx .bit) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product (.storage sink.toCStorageRef) (.storage sink.toCStorageRef)) sink

/-- The original real self-XOR clears found initially and marks the no-pivot case finally. -/
def pivotClearOp (output : CWriteRef ctx .bit) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .xor ctx (.product (.storage output.toCStorageRef) (.storage output.toCStorageRef)) output

/-- Selection flips the previously false actual found latch with the original NOT instruction. -/
def pivotFoundOp (found : CWriteRef ctx .bit) : ClassicalOp .bit .bit ctx ctx :=
  .bit .not ctx (.storage found.toCStorageRef) found

/-- The actual used-row test retains the original most-significant-bit logical row convention. -/
def pivotUsedBit (used : CWriteRef ctx (.unsignedWord rowCount)) (row : Fin rowCount) :
    CInputRef ctx .bit :=
  .wordBitGet (.storage used.toCStorageRef) row

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- A selected row follows the original marker, latch, two records and elimination order. -/
def selectPivot (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width)) (found sink : CWriteRef ctx .bit)
    (pivot : Fin rowCount) (column : Fin width) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (pivotSelectedOp sink))
    (.seq (BitWord.instruction (execution := model) (pivotFoundOp found))
      (.seq (materializePivotRow (model := model) used rows pivot column)
        (.seq (materializePivotColumn (model := model) columns column)
          (eliminateWithPivot (model := model) matrix pivot column))))

/-- The actual matrix bit chooses selection or the real rejected-probe copy. -/
def pivotMatrixChoice (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width)) (found sink : CWriteRef ctx .bit)
    (row : Fin rowCount) (column : Fin width) : CShape.Value .bit → Circuit model ctx ctx
  | .bit false => BitWord.instruction (execution := model) (pivotRejectedOp sink)
  | .bit true => selectPivot (model := model) matrix used rows columns found sink row column

/-- A used row is rejected before reading any matrix bit. -/
def pivotUsedChoice (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width)) (found sink : CWriteRef ctx .bit)
    (row : Fin rowCount) (column : Fin width) : CShape.Value .bit → Circuit model ctx ctx
  | .bit false => .branch (eliminationBit matrix row column)
      (pivotMatrixChoice (model := model) matrix used rows columns found sink row column)
  | .bit true => BitWord.instruction (execution := model) (pivotRejectedOp sink)

/-- The stored found bit suppresses all later probes after the first selected row. -/
def pivotFoundChoice (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width)) (found sink : CWriteRef ctx .bit)
    (row : Fin rowCount) (column : Fin width) : CShape.Value .bit → Circuit model ctx ctx
  | .bit false => .branch (pivotUsedBit used row)
      (pivotUsedChoice (model := model) matrix used rows columns found sink row column)
  | .bit true => .id ctx

/-- A row probe reads the actual found, used and matrix bits in precisely that order. -/
def pivotProbeRow (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width)) (found sink : CWriteRef ctx .bit)
    (row : Fin rowCount) (column : Fin width) : Circuit model ctx ctx :=
  .branch (.storage found.toCStorageRef)
    (pivotFoundChoice (model := model) matrix used rows columns found sink row column)

/-- Only an actual unfound column emits the original no-pivot self-XOR. -/
def pivotAbsentChoice (sink : CWriteRef ctx .bit) : CShape.Value .bit → Circuit model ctx ctx
  | .bit false => BitWord.instruction (execution := model) (pivotClearOp sink)
  | .bit true => .id ctx

/-- The original clear, increasing row scan and final no-pivot branch. -/
def reduceColumnBody (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width)) (found sink : CWriteRef ctx .bit)
    (column : Fin width) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (pivotClearOp found))
    (.seq (Circuit.forRange rowCount
      (fun row => pivotProbeRow (model := model) matrix used rows columns found sink row column))
      (.branch (.storage found.toCStorageRef) (pivotAbsentChoice (model := model) sink)))

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- The first real bit scope holds the original trace sink. -/
@[reducible] def pivotSinkContext (ctx : RuntimeCtx kind) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh

/-- The original found latch is the second real bit scope. -/
@[reducible] def pivotSearchContext (ctx : RuntimeCtx kind) : RuntimeCtx kind :=
  pivotSinkContext (pivotSinkContext ctx)

/-- The current lexical bit is a genuine freshly allocated writable cell. -/
def pivotLatch (ctx : RuntimeCtx kind) : CWriteRef (pivotSinkContext ctx) .bit :=
  CWriteRef.workspaceHead ctx ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh

/-- Original writable inputs retain their keys through both search latches. -/
def pivotSearchWrite {shape : CShape} (output : CWriteRef ctx shape) :
    CWriteRef (pivotSearchContext ctx) shape :=
  (output.underWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh).underWorkspace
    (pivotSinkContext ctx).canonicalFreshKey .bit (pivotSinkContext ctx).canonicalFreshKey_fresh

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The complete search body runs on the original destinations beneath both actual latches. -/
def placedPivotSearch (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width)) (column : Fin width) :
    Circuit model (pivotSearchContext ctx) (pivotSearchContext ctx) :=
  reduceColumnBody (model := model) (pivotSearchWrite matrix) (pivotSearchWrite used)
    (pivotSearchWrite rows)
    (pivotSearchWrite columns) (pivotLatch (pivotSinkContext ctx))
    ((pivotLatch ctx).underWorkspace (pivotSinkContext ctx).canonicalFreshKey .bit
      (pivotSinkContext ctx).canonicalFreshKey_fresh) column

/-- The found latch encloses the complete body and is popped before the outer trace sink. -/
def scopedPivotSearch (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width)) (column : Fin width) :
    Circuit model (pivotSinkContext ctx) (pivotSinkContext ctx) :=
  .workspace (pivotSinkContext ctx) (pivotSinkContext ctx).canonicalFreshKey .bit
    (pivotSinkContext ctx).canonicalFreshKey_fresh
      (placedPivotSearch (model := model) matrix used rows columns column)

/-- One complete original column pass allocates its two bits once, then releases them in order. -/
def reduceColumn (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width)) (column : Fin width) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
    (scopedPivotSearch (model := model) matrix used rows columns column)

end

end QuantumAlg.ClassicalRoutines.GF2.Native
