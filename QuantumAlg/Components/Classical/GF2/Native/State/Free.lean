/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.State.Initialization

/-!
# The actual pivot-mask complement produces the original free-column mask

The represented pivot word comes from the real initialized reduction.
The original fixed-width complement changes that same cell into the pure
free-column mask and preserves every other structural caller read. No
unrepresented machine word is identified with a pure reduction result.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution ClassicalWorkspace

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

omit [BitWord.Selected model] in
private theorem complement_pivot (result : ClassicalAlgorithms.GF2.Result rowCount width) :
    CShape.wordComplement width (.unsignedWord (ClassicalAlgorithms.GF2.pivotColumnMask result)) =
      .unsignedWord (ClassicalAlgorithms.GF2.freeColumnMask result) := by
  apply congrArg CShape.Value.unsignedWord
  apply QuantumAlg.Nat.FixedWidth.word_eq_of_testBit_eq
  intro physical
  change ((2 ^ width - 1 - (ClassicalAlgorithms.GF2.pivotColumnMask result).val) %
    2 ^ width).testBit physical.val =
      (ClassicalAlgorithms.GF2.freeColumnMask result).val.testBit physical.val
  have positive : 0 < 2 ^ width := Nat.two_pow_pos width
  have pivotLt := (ClassicalAlgorithms.GF2.pivotColumnMask result).isLt
  have complementLt : 2 ^ width - 1 -
      (ClassicalAlgorithms.GF2.pivotColumnMask result).val < 2 ^ width := by omega
  rw [Nat.mod_eq_of_lt complementLt]
  have difference : 2 ^ width - 1 - (ClassicalAlgorithms.GF2.pivotColumnMask result).val =
      2 ^ width - ((ClassicalAlgorithms.GF2.pivotColumnMask result).val + 1) := by omega
  rw [difference, Nat.testBit_two_pow_sub_succ pivotLt physical.val]
  simp only [physical.isLt, decide_true, Bool.true_and]
  have logical := ClassicalAlgorithms.GF2.testBit_freeColumnMask_eq_not_testBit_pivotColumnMask
    result (Fin.rev physical)
  simpa only [ClassicalAlgorithms.GF2.testBit, Fin.rev_rev] using logical.symm

omit [BitWord.Selected model] in
/-- One real complement maps a represented pivot word to the original free-column word. -/
theorem gf2ComplementPivotMask_read
    (columns : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (result : ClassicalAlgorithms.GF2.Result rowCount width)
    (represented : store.read (.storage columns.toCStorageRef) =
      .unsignedWord (ClassicalAlgorithms.GF2.pivotColumnMask result)) :
    (store.applyOp (complementPivotMaskOp columns)).read (.storage columns.toCStorageRef) =
      .unsignedWord (ClassicalAlgorithms.GF2.freeColumnMask result) := by
  refine (Store.read_applyOp_output store (complementPivotMaskOp columns)).trans ?_
  change CShape.wordComplement width (store.read (.storage columns.toCStorageRef)) = _
  rw [represented]
  exact complement_pivot result

omit [BitWord.Selected model] in
/-- The original complement writes only its one actual mask destination. -/
theorem gf2ComplementPivotMask_read_other
    (columns : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : columns.key ∉ other.storageKeys) :
    (store.applyOp (complementPivotMaskOp columns)).read other = store.read other :=
  Store.read_applyOp_of_not_mem_storageKeys store (complementPivotMaskOp columns) other separate

omit [BitWord.Selected model] in
/-- The complete actual store differs only by the represented free-column mask write. -/
theorem gf2ComplementPivotMask_store
    (columns : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (result : ClassicalAlgorithms.GF2.Result rowCount width)
    (represented : store.read (.storage columns.toCStorageRef) =
      .unsignedWord (ClassicalAlgorithms.GF2.pivotColumnMask result)) :
    store.applyOp (complementPivotMaskOp columns) =
      store.write columns (.unsignedWord (ClassicalAlgorithms.GF2.freeColumnMask result)) := by
  change store.write columns (CShape.wordComplement width
    (store.read (.storage columns.toCStorageRef))) = _
  rw [represented, complement_pivot result]

/-- The actual initialized increasing-column pass supplies the represented pivot mask. -/
theorem gf2LoadAndReduce_pivotMask {outer : RuntimeCtx model.kind}
    (input : CInputRef outer (.fixedVector rowCount (.bits width)))
    (cells : Cells ctx (stateShapes rowCount width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    (store : Store ctx) (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (inputValues : ∀ row, ClassicalAlgorithms.TerminalDecode.eval
      (TerminalDecode.decodeInput .bigEndian ((store.read (transport.liftInput input)).get row)) =
        samples row) :
    (loadAndReduceStep cells.tail.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.head.ref
      cells.tail.tail.tail.tail.tail.tail.head.ref cells.tail.tail.tail.head.ref
      (transport.liftInput input) store).1.read
        (.storage cells.tail.tail.tail.head.ref.toCStorageRef) =
      .unsignedWord (ClassicalAlgorithms.GF2.pivotColumnMask
        (ClassicalAlgorithms.GF2.reduce samples)) := by
  have represented := gf2LoadAndReduce_cellState input cells distinct transport separated
    store samples inputValues
  refine represented.2.2.2.trans ?_
  apply congrArg CShape.Value.unsignedWord
  apply congrArg ClassicalAlgorithms.GF2.wordOfLogicalBits
  funext column
  rfl

/-- The real reduction followed by its real complement writes the canonical free mask. -/
theorem gf2LoadAndComplement_store {outer : RuntimeCtx model.kind}
    (input : CInputRef outer (.fixedVector rowCount (.bits width)))
    (cells : Cells ctx (stateShapes rowCount width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    (store : Store ctx) (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (inputValues : ∀ row, ClassicalAlgorithms.TerminalDecode.eval
      (TerminalDecode.decodeInput .bigEndian ((store.read (transport.liftInput input)).get row)) =
        samples row) :
    let columns := cells.tail.tail.tail.head.ref
    let reduced := (loadAndReduceStep cells.tail.tail.tail.tail.tail.head.ref
      cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref columns
      (transport.liftInput input) store).1
    reduced.applyOp (complementPivotMaskOp columns) =
      reduced.write columns (.unsignedWord
        (ClassicalAlgorithms.GF2.freeColumnMask (ClassicalAlgorithms.GF2.reduce samples))) := by
  exact gf2ComplementPivotMask_store cells.tail.tail.tail.head.ref _
    (ClassicalAlgorithms.GF2.reduce samples)
    (gf2LoadAndReduce_pivotMask input cells distinct transport separated store samples inputValues)

end

end QuantumAlg.ClassicalRoutines.GF2.Native
