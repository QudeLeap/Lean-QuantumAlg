/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Semantics
import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Materialize.Values
import all QuantumAlg.Components.Classical.GF2.Native.Eliminate.Values
import all QuantumAlg.Components.Classical.GF2.Native.State
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Actual selected-pivot writes in the original seven-cell layout

The real marker instructions, two lexical one-hot masks and full elimination
produce all four original mutable fields. The original allocator supplies the
cell distinctness used internally; no matrix or used-mask alias condition is
added to the algorithm's input domain. This owner states actual field values,
leaving the ordered-column prefix and pure pivot-list interpretation downstream.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution ClassicalWorkspace

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

omit [BitWord.Selected model] in
private lemma avoids {left right : CShape} (output : CWriteRef ctx left)
    (other : CWriteRef ctx right) (separate : output.key ≠ other.key) :
    output.key ∉ (CInputRef.storage other.toCStorageRef).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton] using separate

omit [BitWord.Selected model] in
private lemma shapes_ne {left right : CShape} (output : CWriteRef ctx left)
    (other : CWriteRef ctx right) (different : left ≠ right) : output.key ≠ other.key := by
  intro same
  exact different (CStorageRef.storageRef_shape_eq_of_key output.toCStorageRef
    other.toCStorageRef same)

omit [BitWord.Selected model] in
private lemma marker_read (found sink : CWriteRef ctx .bit) (store : Store ctx)
    {shape : CShape} (other : CWriteRef ctx shape) (nonbit : .bit ≠ shape) :
    ((store.applyOp (pivotSelectedOp sink)).applyOp (pivotFoundOp found)).read
      (.storage other.toCStorageRef) = store.read (.storage other.toCStorageRef) := by
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (pivotFoundOp found) _
      (avoids found other (shapes_ne found other nonbit)),
    Store.read_applyOp_of_not_mem_storageKeys _ (pivotSelectedOp sink) _
      (avoids sink other (shapes_ne sink other nonbit))]

private lemma selected_fields
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width)) (found sink : CWriteRef ctx .bit)
    (pivot : Fin rowCount) (column : Fin width) (store : Store ctx)
    (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (matrixValue : store.read (.storage matrix.toCStorageRef) =
      .fixedVector (fun row => .unsignedWord (samples row)))
    (matrixRows : matrix.key ≠ rows.key) (usedColumns : used.key ≠ columns.key) :
    let final := (selectPivotStep matrix used rows columns found sink pivot column store).1
    (final.read (.storage matrix.toCStorageRef) = .fixedVector (fun row => .unsignedWord
      (ClassicalAlgorithms.GF2.eliminateRows samples pivot column row))) ∧
    ((final.read (.storage used.toCStorageRef)).toNat =
      (store.read (.storage used.toCStorageRef)).toNat ||| 2 ^ (Fin.rev pivot).val) ∧
    (final.read (.storage rows.toCStorageRef) =
      CShape.vectorWrite (store.read (.storage rows.toCStorageRef)) column
        (.unsignedWord (ClassicalAlgorithms.GF2.wordOfLogicalBits
          (fun row => decide (row = pivot))))) ∧
    ((final.read (.storage columns.toCStorageRef)).toNat =
      (store.read (.storage columns.toCStorageRef)).toNat ||| 2 ^ (Fin.rev column).val) := by
  let marked := (store.applyOp (pivotSelectedOp sink)).applyOp (pivotFoundOp found)
  let rowDone := (materializePivotRowStep used rows pivot column marked).1
  let columnDone := (materializePivotColumnStep columns column rowDone).1
  have usedMatrix : used.key ≠ matrix.key := shapes_ne used matrix (by intro same; cases same)
  have columnsMatrix : columns.key ≠ matrix.key :=
    shapes_ne columns matrix (by intro same; cases same)
  have columnsRows : columns.key ≠ rows.key := shapes_ne columns rows (by intro same; cases same)
  have rowsColumns : rows.key ≠ columns.key := columnsRows.symm
  have rowMatrix : rowDone.read (.storage matrix.toCStorageRef) =
      store.read (.storage matrix.toCStorageRef) :=
    (gf2MaterializePivotRow_read_other used rows pivot column marked _
      (avoids used matrix usedMatrix) (avoids rows matrix matrixRows.symm)).trans
        (marker_read found sink store matrix (by intro same; cases same))
  have finalMatrix : columnDone.read (.storage matrix.toCStorageRef) =
      .fixedVector (fun row => .unsignedWord (samples row)) :=
    (gf2MaterializePivotColumn_read_other columns column rowDone _
      (avoids columns matrix columnsMatrix)).trans (rowMatrix.trans matrixValue)
  change (eliminateWithPivotStep matrix pivot column columnDone).1.read _ = _ ∧ _
  refine ⟨gf2EliminateWithPivot_read_matrix matrix pivot column columnDone samples finalMatrix,
    ?_, ?_, ?_⟩
  · change ((eliminateWithPivotStep matrix pivot column columnDone).1.read _).toNat = _
    rw [gf2EliminateWithPivot_read_other matrix pivot column columnDone _
      (avoids matrix used usedMatrix.symm)]
    rw [gf2MaterializePivotColumn_read_other columns column rowDone _
      (avoids columns used usedColumns.symm)]
    rw [gf2MaterializePivotRow_used used rows pivot column marked,
      marker_read found sink store used (by intro same; cases same)]
  · change (eliminateWithPivotStep matrix pivot column columnDone).1.read _ = _
    rw [gf2EliminateWithPivot_read_other matrix pivot column columnDone _
      (avoids matrix rows matrixRows)]
    rw [gf2MaterializePivotColumn_read_other columns column rowDone _
      (avoids columns rows columnsRows)]
    rw [gf2MaterializePivotRow_rows used rows pivot column marked,
      marker_read found sink store rows (by intro same; cases same)]
  · change ((eliminateWithPivotStep matrix pivot column columnDone).1.read _).toNat = _
    rw [gf2EliminateWithPivot_read_other matrix pivot column columnDone _
      (avoids matrix columns columnsMatrix.symm)]
    rw [gf2MaterializePivotColumn_columns columns column rowDone]
    rw [gf2MaterializePivotRow_read_other used rows pivot column marked _
      (avoids used columns usedColumns) (avoids rows columns rowsColumns),
      marker_read found sink store columns (by intro same; cases same)]

/-- Actual selection updates the four original allocated fields with internal separation.

The `distinct` witness is the original allocator's continuation argument, not
an input-domain promise. The two bit markers may be any legitimate same-context
references; their nominal shapes prevent aliases with these four fields.
-/
lemma gf2SelectPivot_cellValues
    (cells : Cells ctx (stateShapes rowCount width)) (distinct : cells.Distinct)
    (found sink : CWriteRef ctx .bit) (pivot : Fin rowCount) (column : Fin width)
    (store : Store ctx) (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (matrixValue : store.read (.storage cells.tail.tail.tail.tail.tail.head.ref.toCStorageRef) =
      .fixedVector (fun row => .unsignedWord (samples row))) :
    let matrix := cells.tail.tail.tail.tail.tail.head.ref
    let used := cells.tail.tail.tail.tail.head.ref
    let rows := cells.tail.tail.tail.tail.tail.tail.head.ref
    let columns := cells.tail.tail.tail.head.ref
    let final := (selectPivotStep matrix used rows columns found sink pivot column store).1
    (final.read (.storage matrix.toCStorageRef) = .fixedVector (fun row => .unsignedWord
      (ClassicalAlgorithms.GF2.eliminateRows samples pivot column row))) ∧
    ((final.read (.storage used.toCStorageRef)).toNat =
      (store.read (.storage used.toCStorageRef)).toNat ||| 2 ^ (Fin.rev pivot).val) ∧
    (final.read (.storage rows.toCStorageRef) =
      CShape.vectorWrite (store.read (.storage rows.toCStorageRef)) column
        (.unsignedWord (ClassicalAlgorithms.GF2.wordOfLogicalBits
          (fun row => decide (row = pivot))))) ∧
    ((final.read (.storage columns.toCStorageRef)).toNat =
      (store.read (.storage columns.toCStorageRef)).toNat ||| 2 ^ (Fin.rev column).val) := by
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
                have matrixRows : matrix.ref.key ≠ rows.ref.key := distinct.2.2.2.2.2.1.1.symm
                have usedColumns : used.ref.key ≠ columns.ref.key := distinct.2.2.2.1.1
                exact selected_fields _ _ _ _ found sink pivot column store samples matrixValue
                  matrixRows usedColumns

end

end QuantumAlg.ClassicalRoutines.GF2.Native
