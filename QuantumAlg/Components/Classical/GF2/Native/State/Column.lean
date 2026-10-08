/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Selected
import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Values

/-!
# Original pure column states in the actual allocated GF(2) fields

The matrix, used-row word and two pivot-record fields are read from the same
real store. The original ordered-column prefix supplies absence of the current
column; allocator distinctness supplies physical separation. Neither fact is
an additional input-domain promise for the complete algorithm.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution ClassicalWorkspace

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

/-- The original four mathematical fields encoded in the actual seven-cell workspace. -/
def columnStateValues (cells : Cells ctx (stateShapes rowCount width)) (store : Store ctx)
    (state : ClassicalAlgorithms.GF2.State rowCount width) : Prop :=
  let lookup := fun column => state.pivots.find? (fun pivot => decide (pivot.column = column))
  (store.read (.storage cells.tail.tail.tail.tail.tail.head.ref.toCStorageRef) =
    .fixedVector (fun row => .unsignedWord (state.rows row))) ∧
  (store.read (.storage cells.tail.tail.tail.tail.head.ref.toCStorageRef) =
    .unsignedWord (ClassicalAlgorithms.GF2.wordOfLogicalBits
      (fun row => decide (row ∈ state.used)))) ∧
  (store.read (.storage cells.tail.tail.tail.tail.tail.tail.head.ref.toCStorageRef) =
    .fixedVector (fun column => match lookup column with
      | none => CShape.wordOfNat rowCount 0
      | some pivot => .unsignedWord (ClassicalAlgorithms.GF2.wordOfLogicalBits
          (fun row => decide (row = pivot.row))))) ∧
  (store.read (.storage cells.tail.tail.tail.head.ref.toCStorageRef) =
    .unsignedWord (ClassicalAlgorithms.GF2.wordOfLogicalBits
      (fun column => (lookup column).isSome)))

omit [BitWord.Selected model] in
private theorem word_or_bits (left right : Fin width → Bool) :
    (ClassicalAlgorithms.GF2.wordOfLogicalBits left).val |||
      (ClassicalAlgorithms.GF2.wordOfLogicalBits right).val =
        (ClassicalAlgorithms.GF2.wordOfLogicalBits (fun index => left index || right index)).val :=
    by
  let combined : ClassicalAlgorithms.Word width :=
    ⟨(ClassicalAlgorithms.GF2.wordOfLogicalBits left).val |||
      (ClassicalAlgorithms.GF2.wordOfLogicalBits right).val,
      Nat.or_lt_two_pow (ClassicalAlgorithms.GF2.wordOfLogicalBits left).isLt
        (ClassicalAlgorithms.GF2.wordOfLogicalBits right).isLt⟩
  have same : combined = ClassicalAlgorithms.GF2.wordOfLogicalBits
      (fun index => left index || right index) := by
    apply QuantumAlg.Nat.FixedWidth.word_eq_of_testBit_eq
    intro physical
    have first := ClassicalAlgorithms.GF2.testBit_wordOfLogicalBits left (Fin.rev physical)
    have second := ClassicalAlgorithms.GF2.testBit_wordOfLogicalBits right (Fin.rev physical)
    have result := ClassicalAlgorithms.GF2.testBit_wordOfLogicalBits
      (fun index => left index || right index) (Fin.rev physical)
    simp only [ClassicalAlgorithms.GF2.testBit, Fin.rev_rev] at first second result
    change Nat.testBit ((ClassicalAlgorithms.GF2.wordOfLogicalBits left).val |||
      (ClassicalAlgorithms.GF2.wordOfLogicalBits right).val) physical.val = _
    rw [Nat.testBit_or, first, second, result]
  exact congrArg Fin.val same

omit [BitWord.Selected model] in
private theorem used_insert (used : Finset (Fin rowCount)) (pivot : Fin rowCount) :
    (ClassicalAlgorithms.GF2.wordOfLogicalBits (fun row => decide (row ∈ used))).val |||
      2 ^ (Fin.rev pivot).val =
        (ClassicalAlgorithms.GF2.wordOfLogicalBits
          (fun row => decide (row ∈ insert pivot used))).val := by
  rw [← ClassicalAlgorithms.GF2.wordOfLogicalBits_singleton_val pivot, word_or_bits]
  congr 2
  funext row
  simp [Finset.mem_insert, Bool.or_comm]

omit [BitWord.Selected model] in
private theorem lookup_append_same (state : ClassicalAlgorithms.GF2.State rowCount width)
    (pivot : Fin rowCount) (column : Fin width)
    (absent : state.pivots.find? (fun entry => decide (entry.column = column)) = none) :
    (state.pivots ++ [(⟨pivot, column⟩ : ClassicalAlgorithms.GF2.Pivot rowCount width)]).find?
      (fun entry => decide (entry.column = column)) = some ⟨pivot, column⟩ := by
  simp [List.find?_append, absent]

omit [BitWord.Selected model] in
private theorem lookup_append_other (state : ClassicalAlgorithms.GF2.State rowCount width)
    (pivot : Fin rowCount) (column other : Fin width) (different : other ≠ column) :
    (state.pivots ++ [(⟨pivot, column⟩ : ClassicalAlgorithms.GF2.Pivot rowCount width)]).find?
      (fun entry => decide (entry.column = other)) =
        state.pivots.find? (fun entry => decide (entry.column = other)) := by
  simp [List.find?_append, different.symm]

omit [BitWord.Selected model] in
private theorem rows_append (state : ClassicalAlgorithms.GF2.State rowCount width)
    (pivot : Fin rowCount) (column : Fin width)
    (absent : state.pivots.find? (fun entry => decide (entry.column = column)) = none) :
    CShape.vectorWrite
      (.fixedVector (fun other => match state.pivots.find?
        (fun entry => decide (entry.column = other)) with
        | none => CShape.wordOfNat rowCount 0
        | some entry => .unsignedWord (ClassicalAlgorithms.GF2.wordOfLogicalBits
            (fun row => decide (row = entry.row))))) column
      (.unsignedWord (ClassicalAlgorithms.GF2.wordOfLogicalBits
        (fun row => decide (row = pivot)))) =
      .fixedVector (fun other => match (state.pivots ++
        [(⟨pivot, column⟩ : ClassicalAlgorithms.GF2.Pivot rowCount width)]).find?
        (fun entry => decide (entry.column = other)) with
        | none => CShape.wordOfNat rowCount 0
        | some entry => .unsignedWord (ClassicalAlgorithms.GF2.wordOfLogicalBits
            (fun row => decide (row = entry.row)))) := by
  apply congrArg CShape.Value.fixedVector
  funext other
  by_cases same : other = column
  · subst other
    simp only [Function.update_self, lookup_append_same state pivot column absent]
  · simp only [Function.update_of_ne same, CShape.Value.get,
      lookup_append_other state pivot column other same]

omit [BitWord.Selected model] in
private theorem columns_append (state : ClassicalAlgorithms.GF2.State rowCount width)
    (pivot : Fin rowCount) (column : Fin width)
    (absent : state.pivots.find? (fun entry => decide (entry.column = column)) = none) :
    (ClassicalAlgorithms.GF2.wordOfLogicalBits (fun other =>
      (state.pivots.find? (fun entry => decide (entry.column = other))).isSome)).val |||
      2 ^ (Fin.rev column).val =
        (ClassicalAlgorithms.GF2.wordOfLogicalBits (fun other =>
          ((state.pivots ++
            [(⟨pivot, column⟩ : ClassicalAlgorithms.GF2.Pivot rowCount width)]).find?
            (fun entry => decide (entry.column = other))).isSome)).val := by
  rw [← ClassicalAlgorithms.GF2.wordOfLogicalBits_singleton_val column, word_or_bits]
  congr 2
  funext other
  by_cases same : other = column
  · subst other
    simp [lookup_append_same state pivot column absent]
  · simp [lookup_append_other state pivot column other same, same]

omit [BitWord.Selected model] in
private theorem word_eq_of_nat (left right : CShape.Value (.unsignedWord width))
    (same : left.toNat = right.toNat) : left = right := by
  cases left with
  | unsignedWord left =>
      cases right with
      | unsignedWord right => exact congrArg CShape.Value.unsignedWord (Fin.ext same)

/-- The actual selected arm realizes the original pure column step on all four fields.

The actual ordered scan supplies `choice`; the original increasing-column
prefix supplies `absent`. These are internal step contracts, not requirements
on an algorithm input or on a host-provided execution result.
-/
theorem gf2SelectPivot_cellState
    (cells : Cells ctx (stateShapes rowCount width)) (distinct : cells.Distinct)
    (found sink : CWriteRef ctx .bit) (pivot : Fin rowCount) (column : Fin width)
    (store : Store ctx) (state : ClassicalAlgorithms.GF2.State rowCount width)
    (represented : columnStateValues cells store state)
    (choice : ClassicalAlgorithms.GF2.firstUnusedPivot state column = some pivot)
    (absent : state.pivots.find? (fun entry => decide (entry.column = column)) = none) :
    columnStateValues cells
      (selectPivotStep cells.tail.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.head.ref
        cells.tail.tail.tail.tail.tail.tail.head.ref cells.tail.tail.tail.head.ref
        found sink pivot column store).1
      (ClassicalAlgorithms.GF2.stepColumn column state) := by
  rcases represented with ⟨matrixValue, usedValue, rowsValue, columnsValue⟩
  obtain ⟨matrixDone, usedDone, rowsDone, columnsDone⟩ :=
    gf2SelectPivot_cellValues cells distinct found sink pivot column store state.rows matrixValue
  simp only [columnStateValues, ClassicalAlgorithms.GF2.stepColumn, choice]
  refine ⟨matrixDone, ?_, ?_, ?_⟩
  · apply word_eq_of_nat
    rw [usedDone, usedValue]
    exact used_insert state.used pivot
  · rw [rowsDone, rowsValue]
    exact rows_append state pivot column absent
  · apply word_eq_of_nat
    rw [columnsDone, columnsValue]
    exact columns_append state pivot column absent

omit [BitWord.Selected model] in
private theorem clear_read (found : CWriteRef ctx .bit) (store : Store ctx)
    {shape : CShape} (other : CWriteRef ctx shape) (nonbit : .bit ≠ shape) :
    (store.applyOp (pivotClearOp found)).read (.storage other.toCStorageRef) =
      store.read (.storage other.toCStorageRef) := by
  apply Store.read_applyOp_of_not_mem_storageKeys
  simp only [CInputRef.storageKeys, List.mem_singleton]
  intro same
  exact nonbit (CStorageRef.storageRef_shape_eq_of_key found.toCStorageRef
    other.toCStorageRef same)

omit [BitWord.Selected model] in
private theorem clear_values (cells : Cells ctx (stateShapes rowCount width))
    (found : CWriteRef ctx .bit) (store : Store ctx)
    (state : ClassicalAlgorithms.GF2.State rowCount width)
    (represented : columnStateValues cells store state) :
    columnStateValues cells (store.applyOp (pivotClearOp found)) state := by
  unfold columnStateValues
  rw [clear_read found store cells.tail.tail.tail.tail.tail.head.ref
        (by intro same; cases same),
      clear_read found store cells.tail.tail.tail.tail.head.ref (by intro same; cases same),
      clear_read found store cells.tail.tail.tail.tail.tail.tail.head.ref
        (by intro same; cases same),
      clear_read found store cells.tail.tail.tail.head.ref (by intro same; cases same)]
  exact represented

omit [BitWord.Selected model] in
private theorem used_value (cells : Cells ctx (stateShapes rowCount width))
    (store : Store ctx) (state : ClassicalAlgorithms.GF2.State rowCount width)
    (represented : columnStateValues cells store state) (row : Fin rowCount) :
    (store.read (pivotUsedBit cells.tail.tail.tail.tail.head.ref row)).toBool =
      decide (row ∈ state.used) := by
  change ((store.read (.storage cells.tail.tail.tail.tail.head.ref.toCStorageRef)).wordBitGet
    row).toBool = _
  rw [represented.2.1]
  exact (ClassicalAlgorithms.GF2.testBit_machine_coordinate
    (ClassicalAlgorithms.GF2.wordOfLogicalBits
      (fun row => decide (row ∈ state.used))) row).symm.trans
      (ClassicalAlgorithms.GF2.testBit_wordOfLogicalBits _ row)

/-- The complete actual scan, including its no-pivot branch, realizes the original column step. -/
theorem gf2ReduceColumnBody_cellState
    (cells : Cells ctx (stateShapes rowCount width)) (distinct : cells.Distinct)
    (found sink : CWriteRef ctx .bit) (column : Fin width)
    (store : Store ctx) (state : ClassicalAlgorithms.GF2.State rowCount width)
    (represented : columnStateValues cells store state)
    (absent : state.pivots.find? (fun entry => decide (entry.column = column)) = none) :
    columnStateValues cells
      (reduceColumnBodyStep cells.tail.tail.tail.tail.tail.head.ref
        cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref
        cells.tail.tail.tail.head.ref found sink column store).1
      (ClassicalAlgorithms.GF2.stepColumn column state) := by
  rw [gf2ReduceColumnBody_of_state _ _ _ _ found sink column store state represented.1
    (used_value cells store state represented)]
  have cleared := clear_values cells found store state represented
  cases choice : ClassicalAlgorithms.GF2.firstUnusedPivot state column with
  | none =>
      simpa only [ClassicalAlgorithms.GF2.stepColumn, choice, columnStateValues] using
        clear_values cells sink (store.applyOp (pivotClearOp found)) state cleared
  | some pivot =>
      exact gf2SelectPivot_cellState cells distinct found sink pivot column
        (store.applyOp (pivotClearOp found)) state cleared choice absent

end

end QuantumAlg.ClassicalRoutines.GF2.Native
