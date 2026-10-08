/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Candidate.Pivot
import all QuantumAlg.Components.Classical.GF2.Native.State
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Separation

/-!
# Original back substitution by the actual GF(2) column and row traversals

The original candidate copy is followed by increasing columns and increasing
rows. The actual store is passed between all iterations. The seven real cells
supply source separation; the original sole-free-column witness interprets
the actual AND tests. Neither witness is an extra complete-algorithm input
condition, and no initial candidate value is required.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution ClassicalWorkspace

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

private theorem rows_other
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (count : Nat) (indices : Fin count → Fin rowCount) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : candidate.key ∉ other.storageKeys) :
    (Circuit.forRangeStoreRecord count
      (fun index => candidatePivotRow matrix rows free candidate zero (indices index) column)
      (fun index => candidatePivotRowStep matrix rows free candidate zero (indices index) column)
      store).1.read other = store.read other := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      change (Circuit.forRangeStoreRecord count _ _
        (candidatePivotRowStep matrix rows free candidate zero (indices 0) column store).1).1.read
          other = _
      exact (ih (fun index => indices index.succ) _).trans
        (gf2CandidatePivotRow_read_other matrix rows free candidate zero (indices 0) column
          store other separate)

private theorem columns_other
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (count : Nat) (indices : Fin count → Fin width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : candidate.key ∉ other.storageKeys) :
    (Circuit.forRangeStoreRecord count
      (fun index => Circuit.forRange rowCount (fun row =>
        candidatePivotRow matrix rows free candidate zero row (indices index)))
      (fun index => Circuit.forRangeStoreRecord rowCount _ (fun row =>
        candidatePivotRowStep matrix rows free candidate zero row (indices index))) store).1.read
          other = store.read other := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      change (Circuit.forRangeStoreRecord count _ _ (Circuit.forRangeStoreRecord rowCount _
        (fun row => candidatePivotRowStep matrix rows free candidate zero row (indices 0))
          store).1).1.read other = _
      exact (ih (fun index => indices index.succ) _).trans
        (rows_other matrix rows free candidate zero (indices 0) rowCount id store other separate)

/-- The actual copy and both original traversals preserve all reads outside the candidate. -/
theorem gf2BuildCandidate_read_other
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : candidate.key ∉ other.storageKeys) :
    (buildCandidateStep matrix rows free candidate zero store).1.read other =
      store.read other := by
  refine (columns_other matrix rows free candidate zero width id
    (store.applyOp (candidateCopyOp free candidate)) other separate).trans ?_
  exact Store.read_applyOp_of_not_mem_storageKeys store (candidateCopyOp free candidate)
    other separate

omit [BitWord.Selected model] in
private def sources
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free zero : CWriteRef ctx (.unsignedWord width))
    (result : ClassicalAlgorithms.GF2.Result rowCount width) (store : Store ctx) : Prop :=
  (store.read (.storage matrix.toCStorageRef) =
    .fixedVector (fun row => .unsignedWord (result.reduced row))) ∧
  (store.read (.storage rows.toCStorageRef) =
    .fixedVector (fun column => match ClassicalAlgorithms.GF2.pivotForColumn? result column with
      | none => CShape.wordOfNat rowCount 0
      | some pivot => .unsignedWord (ClassicalAlgorithms.GF2.wordOfLogicalBits
          (fun row => decide (row = pivot.row))))) ∧
  (store.read (.storage free.toCStorageRef) =
    .unsignedWord (ClassicalAlgorithms.GF2.freeColumnMask result)) ∧
  (store.read (.storage zero.toCStorageRef) = CShape.wordOfNat width 0)

omit [BitWord.Selected model] in
private theorem avoids {left right : CShape} (output : CWriteRef ctx left)
    (other : CWriteRef ctx right) (separate : output.key ≠ other.key) :
    output.key ∉ (CInputRef.storage other.toCStorageRef).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton] using separate

omit [BitWord.Selected model] in
private theorem word_vector_ne {size count : Nat} {shape : CShape}
    (word : CWriteRef ctx (.unsignedWord size))
    (vector : CWriteRef ctx (.fixedVector count shape)) : word.key ≠ vector.key := by
  intro same
  have impossible := CStorageRef.storageRef_shape_eq_of_key word.toCStorageRef
    vector.toCStorageRef same
  cases impossible

omit [BitWord.Selected model] in
private theorem sources_after
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (result : ClassicalAlgorithms.GF2.Result rowCount width) (store after : Store ctx)
    (represented : sources matrix rows free zero result store)
    (freeSeparate : candidate.key ≠ free.key) (zeroSeparate : candidate.key ≠ zero.key)
    (same : ∀ {shape} (other : CInputRef ctx shape), candidate.key ∉ other.storageKeys →
      after.read other = store.read other) : sources matrix rows free zero result after := by
  obtain ⟨matrixValue, rowsValue, freeValue, zeroValue⟩ := represented
  exact ⟨(same _ (avoids candidate matrix (word_vector_ne candidate matrix))).trans matrixValue,
    (same _ (avoids candidate rows (word_vector_ne candidate rows))).trans rowsValue,
    (same _ (avoids candidate free freeSeparate)).trans freeValue,
    (same _ (avoids candidate zero zeroSeparate)).trans zeroValue⟩

omit [BitWord.Selected model] in
private theorem and_value (left right : ClassicalAlgorithms.Word width) :
    (CShape.wordBitAnd width (.unsignedWord left) (.unsignedWord right)).toNat =
      left.val &&& right.val :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left left.isLt)

omit [BitWord.Selected model] in
private theorem power_bit (column target : Fin width) :
    Nat.testBit (2 ^ (Fin.rev column).val) (Fin.rev target).val = decide (target = column) := by
  rw [Nat.testBit_two_pow]
  congr 1
  apply propext
  constructor
  · intro same
    exact (Fin.rev_injective (Fin.ext same)).symm
  · intro same
    subst target
    rfl

private theorem row_bit
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (result : ClassicalAlgorithms.GF2.Result rowCount width) (selected : Fin width)
    (choice : ClassicalAlgorithms.GF2.soleFreeColumn? result = some selected)
    (store : Store ctx) (represented : sources matrix rows free zero result store)
    (row : Fin rowCount) (column target : Fin width) :
    Nat.testBit ((candidatePivotRowStep matrix rows free candidate zero row column store).1.read
      (.storage candidate.toCStorageRef)).toNat (Fin.rev target).val =
      (Nat.testBit (store.read (.storage candidate.toCStorageRef)).toNat (Fin.rev target).val ||
        (decide (target = column) &&
          match ClassicalAlgorithms.GF2.pivotForColumn? result column with
          | none => false
          | some pivot => decide (row = pivot.row) &&
              ClassicalAlgorithms.GF2.testBit (result.reduced row) selected)) := by
  obtain ⟨matrixValue, rowsValue, freeValue, zeroValue⟩ := represented
  rw [gf2CandidatePivotRow_candidate,
    gf2CandidatePivotBit_of_record rows result store rowsValue, matrixValue, freeValue, zeroValue]
  simp only [CShape.Value.get]
  have zeroNat : (CShape.wordOfNat width 0).toNat = 0 := by
    simp only [CShape.wordOfNat, CShape.Value.toNat, Nat.zero_mod]
  rw [and_value, zeroNat]
  cases lookup : ClassicalAlgorithms.GF2.pivotForColumn? result column with
  | none => simp only [Bool.false_eq_true, if_false, Bool.and_false, Bool.or_false]
  | some pivot =>
      by_cases same : row = pivot.row
      · subst row
        simp only [decide_true, if_true, Bool.true_and]
        cases bit : ClassicalAlgorithms.GF2.testBit (result.reduced pivot.row) selected with
        | false =>
            have clear := (ClassicalAlgorithms.GF2.land_freeColumnMask_eq_zero_iff_testBit_eq_false
              choice (result.reduced pivot.row)).mpr bit
            rw [if_pos clear]
            simp only [Bool.and_false, Bool.or_false]
        | true =>
            have nonzero := (ClassicalAlgorithms.GF2.land_freeColumnMask_ne_zero_iff_testBit_eq_true
              choice (result.reduced pivot.row)).mpr bit
            rw [if_neg nonzero, Nat.testBit_or, power_bit]
            simp only [Bool.and_true]
      · simp only [same, decide_false, Bool.false_eq_true, if_false,
          Bool.false_and, Bool.and_false, Bool.or_false]

private theorem rows_bit
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (result : ClassicalAlgorithms.GF2.Result rowCount width) (selected : Fin width)
    (choice : ClassicalAlgorithms.GF2.soleFreeColumn? result = some selected)
    (freeSeparate : candidate.key ≠ free.key)
    (zeroSeparate : candidate.key ≠ zero.key)
    (column target : Fin width) (count : Nat) (indices : Fin count → Fin rowCount)
    (store : Store ctx) (represented : sources matrix rows free zero result store) :
    Nat.testBit ((Circuit.forRangeStoreRecord count
      (fun index => candidatePivotRow matrix rows free candidate zero (indices index) column)
      (fun index => candidatePivotRowStep matrix rows free candidate zero (indices index) column)
      store).1.read (.storage candidate.toCStorageRef)).toNat (Fin.rev target).val =
      (Nat.testBit (store.read (.storage candidate.toCStorageRef)).toNat
        (Fin.rev target).val ||
        (decide (target = column) &&
          match ClassicalAlgorithms.GF2.pivotForColumn? result column with
          | none => false
          | some pivot => decide (pivot.row ∈ List.ofFn indices) &&
              ClassicalAlgorithms.GF2.testBit (result.reduced pivot.row) selected)) := by
  induction count generalizing store with
  | zero =>
      cases lookup : ClassicalAlgorithms.GF2.pivotForColumn? result column <;>
        simp only [Circuit.forRangeStoreRecord, List.ofFn_zero, List.not_mem_nil, decide_false,
          Bool.false_and, Bool.and_false, Bool.or_false]
  | succ count ih =>
      let first := (candidatePivotRowStep matrix rows free candidate zero
        (indices 0) column store).1
      have firstSources : sources matrix rows free zero result first :=
        sources_after matrix rows free candidate zero result store first represented
          freeSeparate zeroSeparate
          (gf2CandidatePivotRow_read_other matrix rows free candidate zero (indices 0) column store)
      change Nat.testBit ((Circuit.forRangeStoreRecord count _ _ first).1.read _).toNat _ = _
      rw [ih (fun index => indices index.succ) first firstSources,
        row_bit matrix rows free candidate zero result selected choice store represented,
        List.ofFn_succ]
      cases lookup : ClassicalAlgorithms.GF2.pivotForColumn? result column with
      | none => simp only [Bool.and_false, Bool.or_false]
      | some pivot =>
          by_cases current : indices 0 = pivot.row
          · rw [current]
            by_cases targetSame : target = column <;>
              cases bit : ClassicalAlgorithms.GF2.testBit (result.reduced pivot.row) selected <;>
              simp [targetSame, bit]
          · have currentRev : pivot.row ≠ indices 0 := Ne.symm current
            simp only [current, decide_false, Bool.false_and, Bool.and_false, Bool.or_false,
              List.mem_cons, currentRev, false_or]

private theorem all_rows_bit
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (result : ClassicalAlgorithms.GF2.Result rowCount width) (selected : Fin width)
    (choice : ClassicalAlgorithms.GF2.soleFreeColumn? result = some selected)
    (freeSeparate : candidate.key ≠ free.key)
    (zeroSeparate : candidate.key ≠ zero.key)
    (column target : Fin width) (store : Store ctx)
    (represented : sources matrix rows free zero result store) :
    Nat.testBit ((Circuit.forRangeStoreRecord rowCount
      (fun row => candidatePivotRow matrix rows free candidate zero row column)
      (fun row => candidatePivotRowStep matrix rows free candidate zero row column)
      store).1.read (.storage candidate.toCStorageRef)).toNat (Fin.rev target).val =
      (Nat.testBit (store.read (.storage candidate.toCStorageRef)).toNat
        (Fin.rev target).val ||
        (decide (target = column) &&
          match ClassicalAlgorithms.GF2.pivotForColumn? result column with
          | none => false
          | some pivot =>
              ClassicalAlgorithms.GF2.testBit (result.reduced pivot.row) selected)) := by
  have actual := rows_bit matrix rows free candidate zero result selected choice
    freeSeparate zeroSeparate column target rowCount id store represented
  cases lookup : ClassicalAlgorithms.GF2.pivotForColumn? result column <;>
    simpa only [lookup, List.mem_ofFn, id_eq, exists_eq, decide_true, Bool.true_and] using actual

private theorem columns_bit
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (result : ClassicalAlgorithms.GF2.Result rowCount width) (selected : Fin width)
    (choice : ClassicalAlgorithms.GF2.soleFreeColumn? result = some selected)
    (freeSeparate : candidate.key ≠ free.key)
    (zeroSeparate : candidate.key ≠ zero.key)
    (target : Fin width) (count : Nat) (indices : Fin count → Fin width)
    (store : Store ctx) (represented : sources matrix rows free zero result store) :
    Nat.testBit ((Circuit.forRangeStoreRecord count
      (fun index => Circuit.forRange rowCount (fun row =>
        candidatePivotRow matrix rows free candidate zero row (indices index)))
      (fun index => Circuit.forRangeStoreRecord rowCount _ (fun row =>
        candidatePivotRowStep matrix rows free candidate zero row (indices index))) store).1.read
          (.storage candidate.toCStorageRef)).toNat (Fin.rev target).val =
      (Nat.testBit (store.read (.storage candidate.toCStorageRef)).toNat
        (Fin.rev target).val ||
        (decide (target ∈ List.ofFn indices) &&
          match ClassicalAlgorithms.GF2.pivotForColumn? result target with
          | none => false
          | some pivot =>
              ClassicalAlgorithms.GF2.testBit (result.reduced pivot.row) selected)) := by
  induction count generalizing store with
  | zero =>
      simp only [Circuit.forRangeStoreRecord, List.ofFn_zero, List.not_mem_nil, decide_false,
        Bool.false_and, Bool.or_false]
  | succ count ih =>
      let first := (Circuit.forRangeStoreRecord rowCount
        (fun row => candidatePivotRow matrix rows free candidate zero row (indices 0))
        (fun row => candidatePivotRowStep matrix rows free candidate zero row (indices 0)) store).1
      have firstSources : sources matrix rows free zero result first :=
        sources_after matrix rows free candidate zero result store first represented
          freeSeparate zeroSeparate
          (rows_other matrix rows free candidate zero (indices 0) rowCount id store)
      change Nat.testBit ((Circuit.forRangeStoreRecord count _ _ first).1.read _).toNat _ = _
      rw [ih (fun index => indices index.succ) first firstSources,
        all_rows_bit matrix rows free candidate zero result selected choice
          freeSeparate zeroSeparate (indices 0) target store represented, List.ofFn_succ]
      by_cases current : target = indices 0
      · subst target
        simp only [decide_true, Bool.true_and, List.mem_cons, true_or, decide_true]
        cases lookup : ClassicalAlgorithms.GF2.pivotForColumn? result (indices 0) with
        | none => simp
        | some pivot =>
            cases bit : ClassicalAlgorithms.GF2.testBit (result.reduced pivot.row) selected <;>
              simp [bit]
      · simp only [current, decide_false, Bool.false_and, Bool.or_false,
          List.mem_cons, false_or]

private theorem build_value
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (result : ClassicalAlgorithms.GF2.Result rowCount width) (selected : Fin width)
    (choice : ClassicalAlgorithms.GF2.soleFreeColumn? result = some selected)
    (freeSeparate : candidate.key ≠ free.key)
    (zeroSeparate : candidate.key ≠ zero.key)
    (store : Store ctx) (represented : sources matrix rows free zero result store) :
    (buildCandidateStep matrix rows free candidate zero store).1.read
      (.storage candidate.toCStorageRef) =
        .unsignedWord (ClassicalAlgorithms.GF2.backSubstitute result selected) := by
  let copied := store.applyOp (candidateCopyOp free candidate)
  have copiedSources : sources matrix rows free zero result copied :=
    sources_after matrix rows free candidate zero result store copied represented
      freeSeparate zeroSeparate
      (fun other separate => Store.read_applyOp_of_not_mem_storageKeys store
        (candidateCopyOp free candidate) other separate)
  have copiedValue : copied.read (.storage candidate.toCStorageRef) =
      .unsignedWord (ClassicalAlgorithms.GF2.freeColumnMask result) :=
    (Store.read_applyOp_output store (candidateCopyOp free candidate)).trans represented.2.2.1
  have bits (target : Fin width) := columns_bit matrix rows free candidate zero result selected
    choice freeSeparate zeroSeparate target width id copied copiedSources
  have finalBits (target : Fin width) :
      Nat.testBit ((buildCandidateStep matrix rows free candidate zero store).1.read
        (.storage candidate.toCStorageRef)).toNat (Fin.rev target).val =
          ClassicalAlgorithms.GF2.testBit (ClassicalAlgorithms.GF2.backSubstitute result selected)
            target := by
    have actual := bits target
    rw [copiedValue] at actual
    simp only [List.mem_ofFn, id_eq, exists_eq, decide_true, Bool.true_and,
      CShape.Value.toNat] at actual
    exact actual.trans
      (ClassicalAlgorithms.GF2.testBit_backSubstitute_eq_freeMask_or_lookup choice target).symm
  cases output : (buildCandidateStep matrix rows free candidate zero store).1.read
    (.storage candidate.toCStorageRef) with
  | unsignedWord word =>
      apply congrArg CShape.Value.unsignedWord
      apply QuantumAlg.Nat.FixedWidth.word_eq_of_testBit_eq
      intro physical
      have original := finalBits (Fin.rev physical)
      simpa only [output, CShape.Value.toNat, Fin.rev_rev, ClassicalAlgorithms.GF2.testBit] using
        original

/-- The original seven cells realize the complete copied and accumulated back-substitution word. -/
theorem gf2BuildCandidate_cellValue
    (cells : Cells ctx (stateShapes rowCount width)) (distinct : cells.Distinct)
    (store : Store ctx) (result : ClassicalAlgorithms.GF2.Result rowCount width)
    (selected : Fin width)
    (choice : ClassicalAlgorithms.GF2.soleFreeColumn? result = some selected)
    (matrixValue : store.read (.storage cells.tail.tail.tail.tail.tail.head.ref.toCStorageRef) =
      .fixedVector (fun row => .unsignedWord (result.reduced row)))
    (rowsValue : store.read (.storage cells.tail.tail.tail.tail.tail.tail.head.ref.toCStorageRef) =
      .fixedVector (fun column => match ClassicalAlgorithms.GF2.pivotForColumn? result column with
        | none => CShape.wordOfNat rowCount 0
        | some pivot => .unsignedWord (ClassicalAlgorithms.GF2.wordOfLogicalBits
            (fun row => decide (row = pivot.row)))))
    (freeValue : store.read (.storage cells.tail.tail.tail.head.ref.toCStorageRef) =
      .unsignedWord (ClassicalAlgorithms.GF2.freeColumnMask result))
    (zeroValue : store.read (.storage cells.tail.head.ref.toCStorageRef) =
      CShape.wordOfNat width 0) :
    (buildCandidateStep cells.tail.tail.tail.tail.tail.head.ref
      cells.tail.tail.tail.tail.tail.tail.head.ref cells.tail.tail.tail.head.ref
      cells.tail.tail.head.ref cells.tail.head.ref store).1.read
        (.storage cells.tail.tail.head.ref.toCStorageRef) =
          .unsignedWord (ClassicalAlgorithms.GF2.backSubstitute result selected) := by
  have keySeparation : cells.tail.tail.head.ref.key ≠ cells.tail.tail.tail.head.ref.key ∧
      cells.tail.tail.head.ref.key ≠ cells.tail.head.ref.key := by
    cases cells with
    | cons success tail0 =>
      cases tail0 with
      | cons zero tail1 =>
        cases tail1 with
        | cons candidate tail2 =>
          cases tail2 with
          | cons columns tail3 =>
              exact ⟨distinct.2.2.1.1.symm, distinct.2.1.1⟩
  exact build_value cells.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.tail.tail.tail.head.ref cells.tail.tail.tail.head.ref
    cells.tail.tail.head.ref cells.tail.head.ref result selected choice
    keySeparation.1 keySeparation.2 store ⟨matrixValue, rowsValue, freeValue, zeroValue⟩

end

end QuantumAlg.ClassicalRoutines.GF2.Native
