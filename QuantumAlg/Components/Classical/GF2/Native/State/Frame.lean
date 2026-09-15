/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.State.Initialization

/-!
# Caller reads through the actual GF(2) loading and reduction prefix

Every original stored branch and ordered loop uses its actual intermediate
store. The four persistent arithmetic destinations are the complete caller
write set; all temporary words and bits are really allocated and popped.
The seven-cell allocator supplies the separation needed to preserve success,
zero and transported caller inputs, with no initial-value or representation
condition.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution ClassicalWorkspace

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

private theorem range_read (count : Nat) (body : Fin count → Circuit ctx ctx)
    (records : ∀ index, Store ctx → Store ctx × (body index).Path)
    {shape : CShape} (other : CInputRef ctx shape)
    (preserves : ∀ index store, (records index store).1.read other = store.read other)
    (store : Store ctx) :
    (Circuit.forRangeRecord count body records store).1.read other = store.read other :=
  Circuit.forRangeRecord_invariant count body records
    (fun _ current => current.read other = store.read other)
    (fun index current same => (preserves index current).trans same) store rfl

section ColumnBody

variable (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
  (used : CWriteRef ctx (.unsignedWord rowCount))
  (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
  (columns : CWriteRef ctx (.unsignedWord width)) (found sink : CWriteRef ctx .bit)
  {shape : CShape} (other : CInputRef ctx shape)
  (matrixFree : matrix.key ∉ other.storageKeys) (usedFree : used.key ∉ other.storageKeys)
  (rowsFree : rows.key ∉ other.storageKeys) (columnsFree : columns.key ∉ other.storageKeys)
  (foundFree : found.key ∉ other.storageKeys) (sinkFree : sink.key ∉ other.storageKeys)

include matrixFree usedFree rowsFree columnsFree foundFree sinkFree

private theorem selected_read (pivot : Fin rowCount) (column : Fin width) (store : Store ctx) :
    (selectPivotStep matrix used rows columns found sink pivot column store).1.read other =
      store.read other := by
  dsimp only [selectPivotStep, Circuit.sequenceRecord]
  rw [gf2EliminateWithPivot_read_other matrix pivot column _ other matrixFree,
    gf2MaterializePivotColumn_read_other columns column _ other columnsFree,
    gf2MaterializePivotRow_read_other used rows pivot column _ other usedFree rowsFree]
  exact (Store.read_applyOp_of_not_mem_storageKeys _ (pivotFoundOp found) other foundFree).trans
    (Store.read_applyOp_of_not_mem_storageKeys store (pivotSelectedOp sink) other sinkFree)

private theorem matrix_choice_read (row : Fin rowCount) (column : Fin width)
    (value : CShape.Value .bit) (store : Store ctx) :
    (pivotMatrixChoiceStep matrix used rows columns found sink row column value store).1.read
      other = store.read other := by
  cases value with
  | bit value =>
    cases value
    · exact Store.read_applyOp_of_not_mem_storageKeys store (pivotRejectedOp sink) other sinkFree
    · exact selected_read matrix used rows columns found sink other matrixFree usedFree rowsFree
        columnsFree foundFree sinkFree row column store

private theorem used_choice_read (row : Fin rowCount) (column : Fin width)
    (value : CShape.Value .bit) (store : Store ctx) :
    (pivotUsedChoiceStep matrix used rows columns found sink row column value store).1.read
      other = store.read other := by
  cases value with
  | bit value =>
    cases value
    · exact matrix_choice_read matrix used rows columns found sink other matrixFree usedFree
        rowsFree columnsFree foundFree sinkFree row column _ store
    · exact Store.read_applyOp_of_not_mem_storageKeys store (pivotRejectedOp sink) other sinkFree

private theorem found_choice_read (row : Fin rowCount) (column : Fin width)
    (value : CShape.Value .bit) (store : Store ctx) :
    (pivotFoundChoiceStep matrix used rows columns found sink row column value store).1.read
      other = store.read other := by
  cases value with
  | bit value =>
    cases value
    · exact used_choice_read matrix used rows columns found sink other matrixFree usedFree
        rowsFree columnsFree foundFree sinkFree row column _ store
    · rfl

private theorem probe_read (row : Fin rowCount) (column : Fin width) (store : Store ctx) :
    (pivotProbeRowStep matrix used rows columns found sink row column store).1.read other =
      store.read other :=
  found_choice_read matrix used rows columns found sink other matrixFree usedFree rowsFree
    columnsFree foundFree sinkFree row column _ store

omit matrixFree usedFree rowsFree columnsFree foundFree in
private theorem absent_read (value : CShape.Value .bit) (store : Store ctx) :
    (pivotAbsentChoiceStep sink value store).1.read other = store.read other := by
  cases value with
  | bit value =>
    cases value
    · exact Store.read_applyOp_of_not_mem_storageKeys store (pivotClearOp sink) other sinkFree
    · rfl

private theorem column_body_read (column : Fin width) (store : Store ctx) :
    (reduceColumnBodyStep matrix used rows columns found sink column store).1.read other =
      store.read other := by
  dsimp only [reduceColumnBodyStep, Circuit.sequenceRecord]
  refine (absent_read sink other sinkFree _ _).trans ?_
  refine (range_read rowCount _ _ other (fun row current =>
    probe_read matrix used rows columns found sink other matrixFree usedFree rowsFree
      columnsFree foundFree sinkFree row column current) _).trans ?_
  exact Store.read_applyOp_of_not_mem_storageKeys store (pivotClearOp found) other foundFree

end ColumnBody

private def searchRead {shape : CShape} (other : CInputRef ctx shape) :
    CInputRef (pivotSearchContext ctx) shape :=
  (other.underWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh).underWorkspace
    (pivotSinkContext ctx).canonicalFreshKey .bit (pivotSinkContext ctx).canonicalFreshKey_fresh

private theorem search_keys {shape : CShape} (other : CInputRef ctx shape) :
    (searchRead other).storageKeys = other.storageKeys := by
  unfold searchRead
  rw [CInputRef.storageKeys_underWorkspace, CInputRef.storageKeys_underWorkspace]

private theorem search_found_fresh {shape : CShape} (other : CInputRef ctx shape) :
    (pivotLatch (pivotSinkContext ctx)).key ∉ (searchRead other).storageKeys := by
  unfold searchRead
  rw [CInputRef.storageKeys_underWorkspace]
  exact fun present => (pivotSinkContext ctx).canonicalFreshKey_fresh
    ((other.underWorkspace ctx.canonicalFreshKey .bit
      ctx.canonicalFreshKey_fresh).storageKeys_subset_context present)

private theorem search_sink_fresh {shape : CShape} (other : CInputRef ctx shape) :
    ((pivotLatch ctx).underWorkspace (pivotSinkContext ctx).canonicalFreshKey .bit
      (pivotSinkContext ctx).canonicalFreshKey_fresh).key ∉ (searchRead other).storageKeys := by
  rw [search_keys]
  exact fun present => ctx.canonicalFreshKey_fresh (other.storageKeys_subset_context present)

/-- Both real pivot-search scopes leave only the original four arithmetic destinations mutable. -/
theorem gf2ReduceColumn_read_other
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width)) (column : Fin width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (matrixFree : matrix.key ∉ other.storageKeys) (usedFree : used.key ∉ other.storageKeys)
    (rowsFree : rows.key ∉ other.storageKeys) (columnsFree : columns.key ∉ other.storageKeys) :
    (reduceColumnStep matrix used rows columns column store).1.read other = store.read other := by
  change (Store.popWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
    (Store.popWorkspace (pivotSinkContext ctx).canonicalFreshKey .bit
      (pivotSinkContext ctx).canonicalFreshKey_fresh _)).read other = _
  rw [Store.read_popWorkspace_underWorkspace, Store.read_popWorkspace_underWorkspace]
  refine (column_body_read (pivotSearchWrite matrix) (pivotSearchWrite used)
    (pivotSearchWrite rows) (pivotSearchWrite columns) (pivotLatch (pivotSinkContext ctx))
    ((pivotLatch ctx).underWorkspace (pivotSinkContext ctx).canonicalFreshKey .bit
      (pivotSinkContext ctx).canonicalFreshKey_fresh) (searchRead other)
    ?_ ?_ ?_ ?_ (search_found_fresh other) (search_sink_fresh other) column _).trans ?_
  · rw [search_keys]
    exact matrixFree
  · rw [search_keys]
    exact usedFree
  · rw [search_keys]
    exact rowsFree
  · rw [search_keys]
    exact columnsFree
  · unfold searchRead
    rw [Store.read_pushWorkspace_underWorkspace, Store.read_pushWorkspace_underWorkspace]

/-- Actual loading and every original reduction stage preserve all other structural reads. -/
theorem gf2LoadAndReduce_read_other
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width))
    (input : CInputRef ctx (.fixedVector rowCount (.bits width))) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (matrixFree : matrix.key ∉ other.storageKeys) (usedFree : used.key ∉ other.storageKeys)
    (rowsFree : rows.key ∉ other.storageKeys) (columnsFree : columns.key ∉ other.storageKeys) :
    (loadAndReduceStep matrix used rows columns input store).1.read other = store.read other := by
  dsimp only [loadAndReduceStep, reduceMatrixStep, Circuit.sequenceRecord]
  refine (range_read width _ _ other (fun column current =>
    gf2ReduceColumn_read_other matrix used rows columns column current other matrixFree
      usedFree rowsFree columnsFree) _).trans ?_
  refine (gf2ClearPivotRows_read_other rows _ other rowsFree).trans ?_
  refine (Store.read_applyOp_of_not_mem_storageKeys _
    (Word.PowerOfTwo.clearOp columns) other columnsFree).trans ?_
  refine (Store.read_applyOp_of_not_mem_storageKeys _
    (Word.PowerOfTwo.clearOp used) other usedFree).trans ?_
  exact range_read rowCount _ _ other
    (fun row current => gf2LoadRow_read_other input matrix row current other matrixFree) store

/-- The original seven-cell placement internally frames success, zero and every caller input. -/
theorem gf2LoadAndReduce_cellFrame {outer : RuntimeCtx kind}
    (input : CInputRef outer (.fixedVector rowCount (.bits width)))
    (cells : Cells ctx (stateShapes rowCount width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    (store : Store ctx) :
    let final := (loadAndReduceStep cells.tail.tail.tail.tail.tail.head.ref
      cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref
      cells.tail.tail.tail.head.ref (transport.liftInput input) store).1
    (final.read (.storage cells.head.ref.toCStorageRef) =
      store.read (.storage cells.head.ref.toCStorageRef)) ∧
    (final.read (.storage cells.tail.head.ref.toCStorageRef) =
      store.read (.storage cells.tail.head.ref.toCStorageRef)) ∧
    (∀ {shape : CShape} (other : CInputRef outer shape),
      final.read (transport.liftInput other) = store.read (transport.liftInput other)) := by
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
                refine ⟨?_, ?_, ?_⟩
                · apply gf2LoadAndReduce_read_other
                  · exact avoids matrix.ref success.ref distinct.1.2.2.2.2.1
                  · exact avoids used.ref success.ref distinct.1.2.2.2.1
                  · exact avoids rows.ref success.ref distinct.1.2.2.2.2.2.1
                  · exact avoids columns.ref success.ref distinct.1.2.2.1
                · apply gf2LoadAndReduce_read_other
                  · exact avoids matrix.ref zero.ref distinct.2.1.2.2.2.1
                  · exact avoids used.ref zero.ref distinct.2.1.2.2.1
                  · exact avoids rows.ref zero.ref distinct.2.1.2.2.2.2.1
                  · exact avoids columns.ref zero.ref distinct.2.1.2.1
                · intro shape other
                  exact gf2LoadAndReduce_read_other matrix.ref used.ref rows.ref columns.ref
                    (transport.liftInput input) store (transport.liftInput other)
                    (separated.2.2.2.2.2.1 other) (separated.2.2.2.2.1 other)
                    (separated.2.2.2.2.2.2.1 other) (separated.2.2.2.1 other)

end

end QuantumAlg.ClassicalRoutines.GF2.Native
