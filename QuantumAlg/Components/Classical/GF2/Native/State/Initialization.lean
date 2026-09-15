/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.State.Traversal
import all QuantumAlg.Components.Classical.GF2.Native.Load.Values
import all QuantumAlg.Components.Classical.GF2.Native.Echelon.Semantics
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Separation

/-!
# Original actual initialization of the seven GF(2) fields

Row loading reads each real intermediate store. Only the original allocator's
structural separation proves that the transported caller samples keep their
values while the fresh matrix is written. The original mask self-XORs and
pivot-row initialization remain actual stages, with no caller-zero promise.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution ClassicalWorkspace

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

private theorem load_rows
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (separate : matrix.key ∉ input.storageKeys) (count : Nat)
    (indices : Fin count → Fin rowCount) (store : Store ctx)
    (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (inputValues : ∀ row, ClassicalAlgorithms.TerminalDecode.eval
      (TerminalDecode.decodeInput .bigEndian ((store.read input).get row)) = samples row) :
    (Circuit.forRangeRecord count (fun index => loadRow input matrix (indices index))
      (fun index => loadRowStep input matrix (indices index)) store).1.read
        (.storage matrix.toCStorageRef) =
      .fixedVector (fun row => if row ∈ List.ofFn indices then .unsignedWord (samples row)
        else (store.read (.storage matrix.toCStorageRef)).get row) := by
  induction count generalizing store with
  | zero =>
      change store.read (.storage matrix.toCStorageRef) = _
      simp only [List.ofFn_zero, List.not_mem_nil, if_false]
      cases store.read (.storage matrix.toCStorageRef)
      rfl
  | succ count ih =>
      let first := (loadRowStep input matrix (indices 0) store).1
      have inputSame : first.read input = store.read input :=
        gf2LoadRow_read_other input matrix (indices 0) store input separate
      have nextInput : ∀ row, ClassicalAlgorithms.TerminalDecode.eval
          (TerminalDecode.decodeInput .bigEndian ((first.read input).get row)) = samples row := by
        intro row
        rw [inputSame]
        exact inputValues row
      have firstMatrix : first.read (.storage matrix.toCStorageRef) =
          CShape.vectorWrite (store.read (.storage matrix.toCStorageRef)) (indices 0)
            (.unsignedWord (samples (indices 0))) := by
        refine (gf2LoadRow_read_matrix input matrix (indices 0) store).trans ?_
        exact congrArg (fun word => CShape.vectorWrite
          (store.read (.storage matrix.toCStorageRef)) (indices 0) (.unsignedWord word))
          (inputValues (indices 0))
      change (Circuit.forRangeRecord count _ _ first).1.read _ = _
      rw [ih (fun index => indices index.succ) first nextInput, firstMatrix, List.ofFn_succ]
      apply congrArg CShape.Value.fixedVector
      funext row
      by_cases later : row ∈ List.ofFn (fun index => indices index.succ)
      · simp only [later, List.mem_cons, or_true, if_true]
      · by_cases current : row = indices 0
        · subst row
          simp only [later, List.mem_cons, true_or, if_true, if_false,
            CShape.vectorWrite, CShape.Value.get, Function.update_self]
        · simp only [later, current, List.mem_cons, or_self, if_false,
            CShape.vectorWrite, CShape.Value.get, Function.update_of_ne current]

private theorem load_matrix
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (separate : matrix.key ∉ input.storageKeys) (store : Store ctx)
    (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (inputValues : ∀ row, ClassicalAlgorithms.TerminalDecode.eval
      (TerminalDecode.decodeInput .bigEndian ((store.read input).get row)) = samples row) :
    (loadMatrixStep input matrix store).1.read (.storage matrix.toCStorageRef) =
      .fixedVector (fun row => .unsignedWord (samples row)) := by
  have loaded := load_rows input matrix separate rowCount id store samples inputValues
  simpa only [loadMatrixStep, List.mem_ofFn, id_eq, exists_eq, if_true] using loaded

/-- The original allocator supplies input separation for every actual matrix-row decode. -/
theorem gf2LoadMatrix_cellRows {outer : RuntimeCtx kind}
    (input : CInputRef outer (.fixedVector rowCount (.bits width)))
    (cells : Cells ctx (stateShapes rowCount width)) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport) (store : Store ctx)
    (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (inputValues : ∀ row, ClassicalAlgorithms.TerminalDecode.eval
      (TerminalDecode.decodeInput .bigEndian ((store.read (transport.liftInput input)).get row)) =
        samples row) :
    (loadMatrixStep (transport.liftInput input)
      cells.tail.tail.tail.tail.tail.head.ref store).1.read
        (.storage cells.tail.tail.tail.tail.tail.head.ref.toCStorageRef) =
      .fixedVector (fun row => .unsignedWord (samples row)) := by
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
                exact load_matrix (transport.liftInput input) matrix.ref
                  (separated.2.2.2.2.2.1 input) store samples inputValues

private theorem row_written
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (zero : CWriteRef ctx (.unsignedWord rowCount)) (column : Fin width) (store : Store ctx) :
    (store.applyOp (pivotRowWriteOp rows zero column)).read (.storage rows.toCStorageRef) =
      CShape.vectorWrite (store.read (.storage rows.toCStorageRef)) column
        (store.read (.storage zero.toCStorageRef)) := by
  refine (Store.read_applyOp_output store (pivotRowWriteOp rows zero column)).trans ?_
  rfl

private theorem row_zero_frame
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (zero : CWriteRef ctx (.unsignedWord rowCount)) (column : Fin width) (store : Store ctx) :
    (store.applyOp (pivotRowWriteOp rows zero column)).read (.storage zero.toCStorageRef) =
      store.read (.storage zero.toCStorageRef) := by
  apply Store.read_applyOp_of_not_mem_storageKeys
  simp only [CInputRef.storageKeys, List.mem_singleton]
  intro same
  have impossible := CStorageRef.storageRef_shape_eq_of_key rows.toCStorageRef
    zero.toCStorageRef same
  cases impossible

private theorem clear_rows
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (zero : CWriteRef ctx (.unsignedWord rowCount)) (count : Nat)
    (indices : Fin count → Fin width) (store : Store ctx)
    (zeroValue : store.read (.storage zero.toCStorageRef) = CShape.wordOfNat rowCount 0) :
    (Circuit.forRangeRecord count
      (fun index => .classical (pivotRowWriteOp rows zero (indices index)))
      (fun index current => (current.applyOp (pivotRowWriteOp rows zero (indices index)), ()))
      store).1.read (.storage rows.toCStorageRef) =
      .fixedVector (fun column => if column ∈ List.ofFn indices then CShape.wordOfNat rowCount 0
        else (store.read (.storage rows.toCStorageRef)).get column) := by
  induction count generalizing store with
  | zero =>
      change store.read (.storage rows.toCStorageRef) = _
      simp only [List.ofFn_zero, List.not_mem_nil, if_false]
      cases store.read (.storage rows.toCStorageRef)
      rfl
  | succ count ih =>
      let first := store.applyOp (pivotRowWriteOp rows zero (indices 0))
      have nextZero : first.read (.storage zero.toCStorageRef) = CShape.wordOfNat rowCount 0 :=
        (row_zero_frame rows zero (indices 0) store).trans zeroValue
      change (Circuit.forRangeRecord count _ _ first).1.read _ = _
      rw [ih (fun index => indices index.succ) first nextZero, row_written, zeroValue,
        List.ofFn_succ]
      apply congrArg CShape.Value.fixedVector
      funext column
      by_cases later : column ∈ List.ofFn (fun index => indices index.succ)
      · simp only [later, List.mem_cons, or_true, if_true]
      · by_cases current : column = indices 0
        · subst column
          simp only [later, List.mem_cons, true_or, if_true, if_false,
            CShape.vectorWrite, CShape.Value.get, Function.update_self]
        · simp only [later, current, List.mem_cons, or_self, if_false,
            CShape.vectorWrite, CShape.Value.get, Function.update_of_ne current]

private theorem clear_rows_other
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (zero : CWriteRef ctx (.unsignedWord rowCount)) (count : Nat)
    (indices : Fin count → Fin width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : rows.key ∉ other.storageKeys) :
    (Circuit.forRangeRecord count
      (fun index => .classical (pivotRowWriteOp rows zero (indices index)))
      (fun index current => (current.applyOp (pivotRowWriteOp rows zero (indices index)), ()))
      store).1.read other = store.read other := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      change (Circuit.forRangeRecord count _ _
        (store.applyOp (pivotRowWriteOp rows zero (indices 0)))).1.read other = _
      exact (ih (fun index => indices index.succ) _).trans
        (Store.read_applyOp_of_not_mem_storageKeys store
          (pivotRowWriteOp rows zero (indices 0)) other separate)

/-- The original real zero-row scope initializes every pivot record, including width zero. -/
theorem gf2ClearPivotRows_read
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount))) (store : Store ctx) :
    (clearPivotRowsStep rows store).1.read (.storage rows.toCStorageRef) =
      .fixedVector (fun _ => CShape.wordOfNat rowCount 0) := by
  change (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
    ctx.canonicalFreshKey_fresh _).read _ = _
  rw [Store.read_popWorkspace_underWorkspace]
  have cleared := clear_rows
    (rows.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh) (pivotMaskCell ctx rowCount) width id
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh) (by rfl)
  change (pivotRowsClearBodyStep
    (rows.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh) (pivotMaskCell ctx rowCount)
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh)).1.read
        (.storage (rows.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
          ctx.canonicalFreshKey_fresh).toCStorageRef) = _
  simpa only [pivotRowsClearBodyStep, List.mem_ofFn, id_eq, exists_eq, if_true] using cleared

/-- The original real row initialization preserves every other caller read through its scope. -/
theorem gf2ClearPivotRows_read_other
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount))) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : rows.key ∉ other.storageKeys) :
    (clearPivotRowsStep rows store).1.read other = store.read other := by
  change (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
    ctx.canonicalFreshKey_fresh _).read _ = _
  rw [Store.read_popWorkspace_underWorkspace]
  have outside : (rows.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh).key ∉
        (other.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
          ctx.canonicalFreshKey_fresh).storageKeys := by
    rw [CInputRef.storageKeys_underWorkspace]
    exact separate
  have unchanged := clear_rows_other
    (rows.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh) (pivotMaskCell ctx rowCount) width id
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh)
    (other.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh) outside
  refine (show (pivotRowsClearBodyStep _ _ _).1.read _ = _ from unchanged).trans ?_
  exact Store.read_pushWorkspace_underWorkspace store _ _ _ other

private theorem word_eq_of_nat {size : Nat} (left right : CShape.Value (.unsignedWord size))
    (same : left.toNat = right.toNat) : left = right := by
  cases left with
  | unsignedWord left =>
      cases right with
      | unsignedWord right => exact congrArg CShape.Value.unsignedWord (Fin.ext same)

private theorem zero_word (size : Nat) :
    CShape.wordOfNat size 0 = .unsignedWord
      (ClassicalAlgorithms.GF2.wordOfLogicalBits (fun _ : Fin size => false)) := by
  let zero : ClassicalAlgorithms.Word size := ⟨0, pow_pos (by decide : 0 < 2) size⟩
  have same : ClassicalAlgorithms.GF2.wordOfLogicalBits (fun _ : Fin size => false) = zero := by
    apply QuantumAlg.Nat.FixedWidth.word_eq_of_testBit_eq
    intro physical
    have bit := ClassicalAlgorithms.GF2.testBit_wordOfLogicalBits
      (fun _ : Fin size => false) (Fin.rev physical)
    simpa only [ClassicalAlgorithms.GF2.testBit, Fin.rev_rev, zero, Nat.zero_testBit] using bit
  simpa only [zero, CShape.wordOfNat, Nat.zero_mod] using
    (congrArg CShape.Value.unsignedWord same).symm

private theorem clear_word (word : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (store.applyOp (Word.PowerOfTwo.clearOp word)).read (.storage word.toCStorageRef) =
      CShape.wordOfNat width 0 := by
  apply word_eq_of_nat
  rw [Word.PowerOfTwo.clear_read]
  simp only [CShape.wordOfNat, CShape.Value.toNat, Nat.zero_mod]

private theorem avoids {left right : CShape} (output : CWriteRef ctx left)
    (other : CWriteRef ctx right) (separate : output.key ≠ other.key) :
    output.key ∉ (CInputRef.storage other.toCStorageRef).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton] using separate

private theorem shapes_ne {left right : CShape} (output : CWriteRef ctx left)
    (other : CWriteRef ctx right) (different : left ≠ right) : output.key ≠ other.key := by
  intro same
  exact different (CStorageRef.storageRef_shape_eq_of_key output.toCStorageRef
    other.toCStorageRef same)

private theorem initialized_fields
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (matrixValue : store.read (.storage matrix.toCStorageRef) =
      .fixedVector (fun row => .unsignedWord (samples row)))
    (matrixRows : matrix.key ≠ rows.key) (usedColumns : used.key ≠ columns.key) :
    let cleared := (store.applyOp (Word.PowerOfTwo.clearOp used)).applyOp
      (Word.PowerOfTwo.clearOp columns)
    let final := (clearPivotRowsStep rows cleared).1
    (final.read (.storage matrix.toCStorageRef) =
      .fixedVector (fun row => .unsignedWord (samples row))) ∧
    (final.read (.storage used.toCStorageRef) = CShape.wordOfNat rowCount 0) ∧
    (final.read (.storage rows.toCStorageRef) =
      .fixedVector (fun _ => CShape.wordOfNat rowCount 0)) ∧
    (final.read (.storage columns.toCStorageRef) = CShape.wordOfNat width 0) := by
  let cleared := (store.applyOp (Word.PowerOfTwo.clearOp used)).applyOp
    (Word.PowerOfTwo.clearOp columns)
  have usedMatrix := shapes_ne used matrix (by intro same; cases same)
  have columnsMatrix := shapes_ne columns matrix (by intro same; cases same)
  have rowsUsed := shapes_ne rows used (by intro same; cases same)
  have rowsColumns := shapes_ne rows columns (by intro same; cases same)
  refine ⟨?_, ?_, gf2ClearPivotRows_read rows cleared, ?_⟩
  · rw [gf2ClearPivotRows_read_other rows cleared _ (avoids rows matrix matrixRows.symm)]
    rw [Store.read_applyOp_of_not_mem_storageKeys _ (Word.PowerOfTwo.clearOp columns) _
      (avoids columns matrix columnsMatrix)]
    rw [Store.read_applyOp_of_not_mem_storageKeys _ (Word.PowerOfTwo.clearOp used) _
      (avoids used matrix usedMatrix)]
    exact matrixValue
  · rw [gf2ClearPivotRows_read_other rows cleared _ (avoids rows used rowsUsed)]
    rw [Store.read_applyOp_of_not_mem_storageKeys _ (Word.PowerOfTwo.clearOp columns) _
      (avoids columns used usedColumns.symm)]
    exact clear_word used store
  · rw [gf2ClearPivotRows_read_other rows cleared _ (avoids rows columns rowsColumns)]
    exact clear_word columns _

/-- The original actual initialization establishes all four initial fields internally. -/
theorem gf2Initialization_cellState {outer : RuntimeCtx kind}
    (input : CInputRef outer (.fixedVector rowCount (.bits width)))
    (cells : Cells ctx (stateShapes rowCount width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    (store : Store ctx) (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (inputValues : ∀ row, ClassicalAlgorithms.TerminalDecode.eval
      (TerminalDecode.decodeInput .bigEndian ((store.read (transport.liftInput input)).get row)) =
        samples row) :
    let matrix := cells.tail.tail.tail.tail.tail.head.ref
    let used := cells.tail.tail.tail.tail.head.ref
    let rows := cells.tail.tail.tail.tail.tail.tail.head.ref
    let columns := cells.tail.tail.tail.head.ref
    let loaded := (loadMatrixStep (transport.liftInput input) matrix store).1
    let cleared := (loaded.applyOp (Word.PowerOfTwo.clearOp used)).applyOp
      (Word.PowerOfTwo.clearOp columns)
    columnStateValues cells (clearPivotRowsStep rows cleared).1
      (ClassicalAlgorithms.GF2.initial samples) := by
  have loaded := gf2LoadMatrix_cellRows input cells transport separated store samples inputValues
  have keySeparation :
      cells.tail.tail.tail.tail.tail.head.ref.key ≠
        cells.tail.tail.tail.tail.tail.tail.head.ref.key ∧
      cells.tail.tail.tail.tail.head.ref.key ≠ cells.tail.tail.tail.head.ref.key := by
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
                  exact ⟨distinct.2.2.2.2.2.1.1.symm, distinct.2.2.2.1.1⟩
  have fields := initialized_fields cells.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.head.ref _ samples loaded keySeparation.1 keySeparation.2
  obtain ⟨matrixDone, usedDone, rowsDone, columnsDone⟩ := fields
  simpa only [columnStateValues, ClassicalAlgorithms.GF2.initial, List.find?_nil,
      Finset.notMem_empty, decide_false, Option.isSome_none] using
    And.intro matrixDone (And.intro (usedDone.trans (zero_word rowCount))
      (And.intro rowsDone (columnsDone.trans (zero_word width))))

/-- Actual loading, initialization and the original increasing pass realize the pure GF(2) state. -/
theorem gf2LoadAndReduce_cellState {outer : RuntimeCtx kind}
    (input : CInputRef outer (.fixedVector rowCount (.bits width)))
    (cells : Cells ctx (stateShapes rowCount width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    (store : Store ctx) (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (inputValues : ∀ row, ClassicalAlgorithms.TerminalDecode.eval
      (TerminalDecode.decodeInput .bigEndian ((store.read (transport.liftInput input)).get row)) =
        samples row) :
    columnStateValues cells
      (loadAndReduceStep cells.tail.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.head.ref
        cells.tail.tail.tail.tail.tail.tail.head.ref cells.tail.tail.tail.head.ref
        (transport.liftInput input) store).1
      (ClassicalAlgorithms.GF2.runColumns (List.finRange width)
        (ClassicalAlgorithms.GF2.initial samples)) := by
  have initialized := gf2Initialization_cellState input cells distinct transport separated
    store samples inputValues
  exact gf2ReduceColumns_cellState cells distinct _ (ClassicalAlgorithms.GF2.initial samples)
    initialized (ClassicalAlgorithms.GF2.initial_pivotColumnsAvoid samples (List.finRange width))

end

end QuantumAlg.ClassicalRoutines.GF2.Native
