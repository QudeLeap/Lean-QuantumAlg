/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Semantics
import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Materialize.Frame
import all QuantumAlg.Components.Classical.GF2.Native.Eliminate.Values
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Original first-eligible selection by the actual GF(2) pivot scan

Rejected probes perform their real self-copy without changing any store value.
The selected arm flips the actual found bit, and its non-bit arithmetic cannot
overwrite that latch. All later actual probes therefore execute their idle
arms. This gives the original first eligible row without a valid-pivot promise.

The final store is the real selected-arm store, or the real no-pivot marker
store. The selected arm's complete `stepColumn` matrix and mask values are a
subsequent contract; no pure state transformer supplies its executable result.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

omit [BitWord.Selected model] in
private lemma write_read (store : Store ctx) {shape : CShape} (output : CWriteRef ctx shape) :
    store.write output (store.read (.storage output.toCStorageRef)) = store :=
  (Store.store_eq_write_of_read_frame store store output _ rfl (fun _ _ => rfl)).symm

omit [BitWord.Selected model] in
private lemma rejected_store (sink : CWriteRef ctx .bit) (store : Store ctx) :
    store.applyOp (pivotRejectedOp sink) = store := by
  change store.write sink (store.read (.storage sink.toCStorageRef)) = store
  exact write_read store sink

omit [BitWord.Selected model] in
private lemma selected_store (sink : CWriteRef ctx .bit) (store : Store ctx) :
    store.applyOp (pivotSelectedOp sink) = store := by
  have selfAnd (value : CShape.Value .bit) :
      Resource.BitOpcode.eval .and (.product value value) = value := by
    cases value with
    | bit value => cases value <;> rfl
  have evaluated : (pivotSelectedOp sink).eval (store.read (pivotSelectedOp sink).inputRef) =
      store.read (.storage sink.toCStorageRef) := selfAnd _
  change store.write sink _ = store
  rw [evaluated]
  exact write_read store sink

omit [BitWord.Selected model] in
private lemma word_avoids_bit {size : Nat} (word : CWriteRef ctx (.unsignedWord size))
    (bit : CWriteRef ctx .bit) :
    word.key ∉ (CInputRef.storage bit.toCStorageRef).storageKeys := by
  simp only [CInputRef.storageKeys, List.mem_singleton]
  intro same
  have impossible := CStorageRef.storageRef_shape_eq_of_key word.toCStorageRef
    bit.toCStorageRef same
  cases impossible

omit [BitWord.Selected model] in
private lemma vector_avoids_bit {count : Nat} {shape : CShape}
    (vector : CWriteRef ctx (.fixedVector count shape)) (bit : CWriteRef ctx .bit) :
    vector.key ∉ (CInputRef.storage bit.toCStorageRef).storageKeys := by
  simp only [CInputRef.storageKeys, List.mem_singleton]
  intro same
  have impossible := CStorageRef.storageRef_shape_eq_of_key vector.toCStorageRef
    bit.toCStorageRef same
  cases impossible

variable (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
  (used : CWriteRef ctx (.unsignedWord rowCount))
  (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
  (columns : CWriteRef ctx (.unsignedWord width)) (found sink : CWriteRef ctx .bit)

private lemma selected_found (pivot : Fin rowCount) (column : Fin width) (store : Store ctx) :
    (selectPivotStep matrix used rows columns found sink pivot column store).1.read
      (.storage found.toCStorageRef) =
        .bit (!(store.read (.storage found.toCStorageRef)).toBool) := by
  change (eliminateWithPivotStep matrix pivot column
    (materializePivotColumnStep columns column
      (materializePivotRowStep used rows pivot column
        ((store.applyOp (pivotSelectedOp sink)).applyOp (pivotFoundOp found))).1).1).1.read
          (.storage found.toCStorageRef) = _
  rw [gf2EliminateWithPivot_read_other matrix pivot column _ _ (vector_avoids_bit matrix found),
    gf2MaterializePivotColumn_read_other columns column _ _ (word_avoids_bit columns found),
    gf2MaterializePivotRow_read_other used rows pivot column _ _
      (word_avoids_bit used found) (vector_avoids_bit rows found), selected_store sink store]
  refine (Store.read_applyOp_output store (pivotFoundOp found)).trans ?_
  have flipped (value : CShape.Value .bit) :
      Resource.BitOpcode.eval .not value = .bit (!value.toBool) := by
    cases value
    rfl
  exact flipped _

private def eligible (row : Fin rowCount) (column : Fin width) (store : Store ctx) : Bool :=
  !(store.read (pivotUsedBit used row)).toBool &&
    (store.read (eliminationBit matrix row column)).toBool

private lemma matrix_choice_store (row : Fin rowCount) (column : Fin width)
    (value : CShape.Value .bit) (store : Store ctx) :
    (pivotMatrixChoiceStep matrix used rows columns found sink row column value store).1 =
      if value.toBool then
        (selectPivotStep matrix used rows columns found sink row column store).1
      else store := by
  cases value with
  | bit value =>
      cases value
      · exact rejected_store sink store
      · rfl

private lemma used_choice_store (row : Fin rowCount) (column : Fin width)
    (value : CShape.Value .bit) (store : Store ctx) :
    (pivotUsedChoiceStep matrix used rows columns found sink row column value store).1 =
      if value.toBool then store
      else if (store.read (eliminationBit matrix row column)).toBool then
        (selectPivotStep matrix used rows columns found sink row column store).1
      else store := by
  cases value with
  | bit value =>
      cases value
      · exact matrix_choice_store matrix used rows columns found sink row column _ store
      · exact rejected_store sink store

private lemma found_choice_store (row : Fin rowCount) (column : Fin width)
    (value : CShape.Value .bit) (store : Store ctx) :
    (pivotFoundChoiceStep matrix used rows columns found sink row column value store).1 =
      if value.toBool then store
      else if eligible matrix used row column store then
        (selectPivotStep matrix used rows columns found sink row column store).1
      else store := by
  cases value with
  | bit value =>
      cases value
      · change (pivotUsedChoiceStep matrix used rows columns found sink row column
          (store.read (pivotUsedBit used row)) store).1 =
          if eligible matrix used row column store then
            (selectPivotStep matrix used rows columns found sink row column store).1
          else store
        rw [used_choice_store]
        unfold eligible
        cases (store.read (pivotUsedBit used row)).toBool <;> rfl
      · rfl

private lemma probe_store (row : Fin rowCount) (column : Fin width) (store : Store ctx) :
    (pivotProbeRowStep matrix used rows columns found sink row column store).1 =
      if (store.read (.storage found.toCStorageRef)).toBool then store
      else if eligible matrix used row column store then
        (selectPivotStep matrix used rows columns found sink row column store).1
      else store :=
  found_choice_store matrix used rows columns found sink row column _ store

private lemma scan_found (count : Nat) (indices : Fin count → Fin rowCount)
    (column : Fin width) (store : Store ctx)
    (already : store.read (.storage found.toCStorageRef) = .bit true) :
    (Circuit.forRangeStoreRecord count
      (fun index => pivotProbeRow (model := model)
        matrix used rows columns found sink (indices index) column)
      (fun index => pivotProbeRowStep matrix used rows columns found sink (indices index) column)
      store).1 = store := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      change (Circuit.forRangeStoreRecord count _ _
        (pivotProbeRowStep matrix used rows columns found sink (indices 0) column store).1).1 = _
      rw [probe_store, already]
      exact ih (fun index => indices index.succ) store already

private lemma scan_first (count : Nat) (indices : Fin count → Fin rowCount)
    (column : Fin width) (store : Store ctx)
    (unfound : store.read (.storage found.toCStorageRef) = .bit false) :
    (Circuit.forRangeStoreRecord count
      (fun index => pivotProbeRow (model := model)
        matrix used rows columns found sink (indices index) column)
      (fun index => pivotProbeRowStep matrix used rows columns found sink (indices index) column)
      store).1 =
        match Fin.find? (fun index => eligible matrix used (indices index) column store) with
        | none => store
        | some index =>
            (selectPivotStep matrix used rows columns found sink (indices index) column store).1 :=
    by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      change (Circuit.forRangeStoreRecord count _ _
        (pivotProbeRowStep matrix used rows columns found sink (indices 0) column store).1).1 = _
      rw [probe_store, unfound, Fin.find?_succ]
      by_cases active : eligible matrix used (indices 0) column store = true
      · simp only [CShape.Value.toBool, Bool.false_eq_true, if_false, if_pos active]
        apply scan_found
        rw [selected_found, unfound]
        rfl
      · simp only [CShape.Value.toBool, Bool.false_eq_true, if_false, if_neg active]
        have later := ih (fun index => indices index.succ) store unfound
        refine later.trans ?_
        cases Fin.find? (fun index => eligible matrix used (indices index.succ) column store) <;>
          rfl

omit [BitWord.Selected model] in
private lemma cleared_found (store : Store ctx) :
    (store.applyOp (pivotClearOp found)).read (.storage found.toCStorageRef) = .bit false := by
  refine (Store.read_applyOp_output store (pivotClearOp found)).trans ?_
  have selfXor (value : CShape.Value .bit) :
      Resource.BitOpcode.eval .xor (.product value value) = .bit false := by
    cases value with
    | bit value => cases value <;> rfl
  exact selfXor _

omit [BitWord.Selected model] in
private lemma cleared_eligible (row : Fin rowCount) (column : Fin width) (store : Store ctx) :
    eligible matrix used row column (store.applyOp (pivotClearOp found)) =
      eligible matrix used row column store := by
  have usedNe : used.key ≠ found.key := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using word_avoids_bit used found
  have matrixNe : matrix.key ≠ found.key := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using vector_avoids_bit matrix found
  have usedFree : found.key ∉ (pivotUsedBit used row).storageKeys := by
    simpa only [pivotUsedBit, CInputRef.storageKeys, List.mem_singleton] using Ne.symm usedNe
  have matrixFree : found.key ∉ (eliminationBit matrix row column).storageKeys := by
    simpa only [eliminationBit, CInputRef.storageKeys, List.mem_singleton] using Ne.symm matrixNe
  unfold eligible
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (pivotClearOp found) _ usedFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (pivotClearOp found) _ matrixFree]

/-- The actual increasing scan executes the selected arm of exactly the first eligible row. -/
lemma gf2ReduceColumnBody_store (column : Fin width) (store : Store ctx) :
    (reduceColumnBodyStep matrix used rows columns found sink column store).1 =
      match Fin.find? (fun row => !(store.read (pivotUsedBit used row)).toBool &&
        (store.read (eliminationBit matrix row column)).toBool) with
      | none => (store.applyOp (pivotClearOp found)).applyOp (pivotClearOp sink)
      | some pivot => (selectPivotStep matrix used rows columns found sink pivot column
          (store.applyOp (pivotClearOp found))).1 := by
  let cleared := store.applyOp (pivotClearOp found)
  have scan := scan_first matrix used rows columns found sink rowCount (fun row => row)
    column cleared (cleared_found found store)
  have predicate : (fun row => eligible matrix used row column cleared) =
      (fun row => eligible matrix used row column store) := by
    funext row
    exact cleared_eligible matrix used found row column store
  rw [predicate] at scan
  change (pivotAbsentChoiceStep sink
    ((Circuit.forRangeStoreRecord rowCount _ _ cleared).1.read (.storage found.toCStorageRef))
    (Circuit.forRangeStoreRecord rowCount _ _ cleared).1).1 = _
  rw [scan]
  change _ = match Fin.find? (fun row => eligible matrix used row column store) with
    | none => cleared.applyOp (pivotClearOp sink)
    | some pivot => (selectPivotStep matrix used rows columns found sink pivot column cleared).1
  cases choice : Fin.find? (fun row => eligible matrix used row column store) with
  | none =>
      rw [cleared_found found store]
      rfl
  | some pivot =>
      rw [selected_found, cleared_found found store]
      rfl

/-- The original pure first-pivot choice indexes the actual selected-arm store without promises. -/
lemma gf2ReduceColumnBody_of_state (column : Fin width) (store : Store ctx)
    (state : ClassicalAlgorithms.GF2.State rowCount width)
    (matrixValue : store.read (.storage matrix.toCStorageRef) =
      .fixedVector (fun row => .unsignedWord (state.rows row)))
    (usedValue : ∀ row, (store.read (pivotUsedBit used row)).toBool = decide (row ∈ state.used)) :
    (reduceColumnBodyStep matrix used rows columns found sink column store).1 =
      match ClassicalAlgorithms.GF2.firstUnusedPivot state column with
      | none => (store.applyOp (pivotClearOp found)).applyOp (pivotClearOp sink)
      | some pivot => (selectPivotStep matrix used rows columns found sink pivot column
          (store.applyOp (pivotClearOp found))).1 := by
  have predicate : (fun row => !(store.read (pivotUsedBit used row)).toBool &&
      (store.read (eliminationBit matrix row column)).toBool) =
        ClassicalAlgorithms.GF2.pivotPredicate state column := by
    funext row
    rw [usedValue, gf2EliminationBit_of_rows matrix row column store state.rows matrixValue]
    simp [ClassicalAlgorithms.GF2.pivotPredicate]
  rw [gf2ReduceColumnBody_store, predicate]
  rfl

end

end QuantumAlg.ClassicalRoutines.GF2.Native
