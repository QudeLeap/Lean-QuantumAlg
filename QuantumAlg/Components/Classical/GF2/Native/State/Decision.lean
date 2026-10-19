/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.State.Free
import all QuantumAlg.Components.Classical.GF2.Native.State.Frame
import all QuantumAlg.Components.Classical.GF2.Native.Decision.Canonical
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Initialization

/-!
# The actual initialized GF(2) prefix reaches the original candidate decision

The same real loading and reduction are followed by the original complement,
success NOT and scoped uniqueness test. Actual lexical initialization supplies
the original zero and false cells. The input equation only decodes the caller's
original samples. Both the success criterion and the surviving arithmetic
fields refer to the original reduction of those samples.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution ClassicalWorkspace

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

omit [BitWord.Selected model] in
private lemma typed_avoid {left right : CShape} (output : CWriteRef ctx left)
    (other : CWriteRef ctx right) (different : left ≠ right) :
    output.key ∉ (CInputRef.storage other.toCStorageRef).storageKeys :=
  avoids output other (shapes_ne output other different)

omit [BitWord.Selected model] in
private lemma flip_read (success : CWriteRef ctx .bit) (store : Store ctx) :
    (store.applyOp (pivotFoundOp success)).read (.storage success.toCStorageRef) =
      .bit (!(store.read (.storage success.toCStorageRef)).toBool) := by
  refine (Store.read_applyOp_output store (pivotFoundOp success)).trans ?_
  change Resource.BitOpcode.eval .not (store.read (.storage success.toCStorageRef)) = _
  cases store.read (.storage success.toCStorageRef)
  rfl

private lemma decision_suffix_read
    (columns zero : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (columnsFree : columns.key ∉ other.storageKeys)
    (successFree : success.key ∉ other.storageKeys) :
    let enabled := (store.applyOp (complementPivotMaskOp columns)).applyOp (pivotFoundOp success)
    (selectUniqueFreeStep columns zero success enabled).1.read other = store.read other := by
  refine (gf2UniqueFree_read_other columns zero success _ other successFree).trans ?_
  refine (Store.read_applyOp_of_not_mem_storageKeys _ (pivotFoundOp success)
    other successFree).trans ?_
  exact gf2ComplementPivotMask_read_other columns store other columnsFree

omit [BitWord.Selected model] in
private lemma allocation_values
    (cells : Cells ctx (stateShapes rowCount width)) (distinct : cells.Distinct)
    (store : Store ctx) (initialized : cells.Initialized store) :
    (store.read (.storage cells.head.ref.toCStorageRef) = .bit false) ∧
    (store.read (.storage cells.tail.head.ref.toCStorageRef) = CShape.wordOfNat width 0) ∧
    (store.read (.storage cells.tail.tail.head.ref.toCStorageRef) = CShape.wordOfNat width 0) ∧
    (cells.tail.tail.tail.head.ref.key ≠ cells.tail.head.ref.key) ∧
    (cells.tail.tail.tail.head.ref.key ≠ cells.tail.tail.head.ref.key) ∧
    (cells.tail.tail.tail.tail.head.ref.key ≠ cells.tail.tail.head.ref.key) := by
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
                exact ⟨initialized.1, initialized.2.1, initialized.2.2.1,
                  distinct.2.1.2.1, distinct.2.2.1.1, distinct.2.2.1.2.1⟩

omit [BitWord.Selected model] in
private lemma allocation_caller {outer : RuntimeCtx model.kind}
    (cells : Cells ctx (stateShapes rowCount width)) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport)
    {shape : CShape} (other : CInputRef outer shape) :
    (cells.head.ref.key ∉ (transport.liftInput other).storageKeys) ∧
    (cells.tail.tail.tail.head.ref.key ∉ (transport.liftInput other).storageKeys) := by
  cases cells with
  | cons success tail0 =>
    cases tail0 with
    | cons zero tail1 =>
      cases tail1 with
      | cons candidate tail2 =>
        cases tail2 with
        | cons columns tail3 =>
          exact ⟨separated.1 other, separated.2.2.2.1 other⟩

/-- The actual candidate-entry store has the original decision and every required original field. -/
lemma gf2Decision_cellValues {outer : RuntimeCtx model.kind}
    (input : CInputRef outer (.fixedVector rowCount (.bits width)))
    (cells : Cells ctx (stateShapes rowCount width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    (store : Store ctx) (initialized : cells.Initialized store)
    (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (inputValues : ∀ row, ClassicalAlgorithms.TerminalDecode.eval
      (TerminalDecode.decodeInput .bigEndian ((store.read (transport.liftInput input)).get row)) =
        samples row) :
    let matrix := cells.tail.tail.tail.tail.tail.head.ref
    let used := cells.tail.tail.tail.tail.head.ref
    let rows := cells.tail.tail.tail.tail.tail.tail.head.ref
    let columns := cells.tail.tail.tail.head.ref
    let candidate := cells.tail.tail.head.ref
    let zero := cells.tail.head.ref
    let success := cells.head.ref
    let result := ClassicalAlgorithms.GF2.reduce samples
    let reduced := (loadAndReduceStep matrix used rows columns (transport.liftInput input) store).1
    let enabled := (reduced.applyOp (complementPivotMaskOp columns)).applyOp (pivotFoundOp success)
    let final := (selectUniqueFreeStep columns zero success enabled).1
    ((final.read (.storage success.toCStorageRef)).toBool = true ↔
      ∃ column, ClassicalAlgorithms.GF2.soleFreeColumn? result = some column) ∧
    (final.read (.storage matrix.toCStorageRef) =
      .fixedVector (fun row => .unsignedWord (result.reduced row))) ∧
    (final.read (.storage rows.toCStorageRef) =
      .fixedVector (fun column => match ClassicalAlgorithms.GF2.pivotForColumn? result column with
        | none => CShape.wordOfNat rowCount 0
        | some pivot => .unsignedWord (ClassicalAlgorithms.GF2.wordOfLogicalBits
            (fun row => decide (row = pivot.row))))) ∧
    (final.read (.storage columns.toCStorageRef) =
      .unsignedWord (ClassicalAlgorithms.GF2.freeColumnMask result)) ∧
    (final.read (.storage zero.toCStorageRef) = CShape.wordOfNat width 0) ∧
    (final.read (.storage candidate.toCStorageRef) = CShape.wordOfNat width 0) ∧
    (∀ {shape : CShape} (other : CInputRef outer shape),
      final.read (transport.liftInput other) = store.read (transport.liftInput other)) := by
  let matrix := cells.tail.tail.tail.tail.tail.head.ref
  let used := cells.tail.tail.tail.tail.head.ref
  let rows := cells.tail.tail.tail.tail.tail.tail.head.ref
  let columns := cells.tail.tail.tail.head.ref
  let candidate := cells.tail.tail.head.ref
  let zero := cells.tail.head.ref
  let success := cells.head.ref
  let result := ClassicalAlgorithms.GF2.reduce samples
  let reduced := (loadAndReduceStep matrix used rows columns (transport.liftInput input) store).1
  let masked := reduced.applyOp (complementPivotMaskOp columns)
  let enabled := masked.applyOp (pivotFoundOp success)
  let final := (selectUniqueFreeStep columns zero success enabled).1
  have facts := allocation_values cells distinct store initialized
  have arithmetic := gf2LoadAndReduce_cellState input cells distinct transport separated
    store samples inputValues
  have originalFrame := gf2LoadAndReduce_cellFrame input cells distinct transport separated store
  have pivotValue := gf2LoadAndReduce_pivotMask input cells distinct transport separated
    store samples inputValues
  have reducedSuccess : reduced.read (.storage success.toCStorageRef) = .bit false :=
    originalFrame.1.trans facts.1
  have reducedZero : reduced.read (.storage zero.toCStorageRef) = CShape.wordOfNat width 0 :=
    originalFrame.2.1.trans facts.2.1
  have maskSuccess := typed_avoid columns success (by intro same; cases same)
  have successMask := typed_avoid success columns (by intro same; cases same)
  have successZero := typed_avoid success zero (by intro same; cases same)
  have maskZero := avoids columns zero facts.2.2.2.1
  have maskedSuccess : masked.read (.storage success.toCStorageRef) = .bit false :=
    (gf2ComplementPivotMask_read_other columns reduced _ maskSuccess).trans reducedSuccess
  have enabledSuccess : enabled.read (.storage success.toCStorageRef) = .bit true := by
    rw [flip_read success masked, maskedSuccess]
    rfl
  have enabledFree : enabled.read (.storage columns.toCStorageRef) =
      .unsignedWord (ClassicalAlgorithms.GF2.freeColumnMask result) :=
    (Store.read_applyOp_of_not_mem_storageKeys masked (pivotFoundOp success) _ successMask).trans
      (gf2ComplementPivotMask_read columns reduced result pivotValue)
  have enabledZero : enabled.read (.storage zero.toCStorageRef) = CShape.wordOfNat width 0 :=
    (Store.read_applyOp_of_not_mem_storageKeys masked (pivotFoundOp success) _ successZero).trans
      ((gf2ComplementPivotMask_read_other columns reduced _ maskZero).trans reducedZero)
  have accepted := gf2UniqueFree_success_iff columns zero success enabled result
    enabledFree enabledZero
  have matrixFrame : final.read (.storage matrix.toCStorageRef) =
      reduced.read (.storage matrix.toCStorageRef) :=
    decision_suffix_read columns zero success reduced _
      (typed_avoid columns matrix (by intro same; cases same))
      (typed_avoid success matrix (by intro same; cases same))
  have rowsFrame : final.read (.storage rows.toCStorageRef) =
      reduced.read (.storage rows.toCStorageRef) :=
    decision_suffix_read columns zero success reduced _
      (typed_avoid columns rows (by intro same; cases same))
      (typed_avoid success rows (by intro same; cases same))
  have candidateReduced : reduced.read (.storage candidate.toCStorageRef) =
      CShape.wordOfNat width 0 :=
    (gf2LoadAndReduce_read_other matrix used rows columns (transport.liftInput input) store _
      (typed_avoid matrix candidate (by intro same; cases same))
      (avoids used candidate facts.2.2.2.2.2)
      (typed_avoid rows candidate (by intro same; cases same))
      (avoids columns candidate facts.2.2.2.2.1)).trans facts.2.2.1
  refine ⟨?_, matrixFrame.trans arithmetic.1, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [enabledSuccess, CShape.Value.toBool, true_and] using accepted
  · refine rowsFrame.trans ?_
    exact arithmetic.2.2.1
  · exact (gf2UniqueFree_read_other columns zero success enabled _ successMask).trans enabledFree
  · exact (gf2UniqueFree_read_other columns zero success enabled _ successZero).trans enabledZero
  · exact (decision_suffix_read columns zero success reduced _
      (avoids columns candidate facts.2.2.2.2.1)
      (typed_avoid success candidate (by intro same; cases same))).trans candidateReduced
  · intro shape other
    have outside := allocation_caller cells transport separated other
    exact (decision_suffix_read columns zero success reduced (transport.liftInput other)
      outside.2 outside.1).trans (originalFrame.2.2 other)

end

end QuantumAlg.ClassicalRoutines.GF2.Native
