/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Union.Store

/-!
# Reads and writes preserve the actual disjoint storage frame

The lifted instruction references act on exactly their original cells.
Writing in one context leaves the entire other store unchanged, rather
than merely preserving its classical marginal. These structural laws
retain the block labels needed for arbitrary classical, quantum and
external-reference correlations in the interpreter.
-/

namespace QuantumAlg.Execution.ContextUnion

private lemma read_joinCells_left {kind : ProblemKind} {target : RuntimeEntry kind}
    {left : List (RuntimeEntry kind)} (right : List (RuntimeEntry kind))
    (first : Cells left) (second : Cells right) (slot : RuntimeEntrySlot target left) :
    Cells.read (joinCells left right first second) (slotLeft right slot) =
      Cells.read first slot := by
  induction slot with
  | here => rfl
  | there next ih => exact ih first.2

private lemma read_joinCells_right {kind : ProblemKind} {target : RuntimeEntry kind}
    (left : List (RuntimeEntry kind)) {right : List (RuntimeEntry kind)}
    (first : Cells left) (second : Cells right) (slot : RuntimeEntrySlot target right) :
    Cells.read (joinCells left right first second) (slotRight left slot) =
      Cells.read second slot := by
  induction left with
  | nil => rfl
  | cons head tail ih => exact ih first.2

private lemma write_joinCells_left {kind : ProblemKind} {target : RuntimeEntry kind}
    {left : List (RuntimeEntry kind)} (right : List (RuntimeEntry kind))
    (first : Cells left) (second : Cells right) (slot : RuntimeEntrySlot target left)
    (value : CellValue target) :
    Cells.write (joinCells left right first second) (slotLeft right slot) value =
      joinCells left right (Cells.write first slot value) second := by
  induction slot with
  | here => rfl
  | there next ih => exact congrArg (Prod.mk first.1) (ih first.2)

private lemma write_joinCells_right {kind : ProblemKind} {target : RuntimeEntry kind}
    (left : List (RuntimeEntry kind)) {right : List (RuntimeEntry kind)}
    (first : Cells left) (second : Cells right) (slot : RuntimeEntrySlot target right)
    (value : CellValue target) :
    Cells.write (joinCells left right first second) (slotRight left slot) value =
      joinCells left right first (Cells.write second slot value) := by
  induction left with
  | nil => rfl
  | cons head tail ih => exact congrArg (Prod.mk first.1) (ih first.2)

private lemma read_mapInput {kind : ProblemKind} {first second : RuntimeCtx kind}
    (original : Store first) (framed : Store second)
    (lift : ∀ {shape}, CStorageRef first shape → CStorageRef second shape)
    (reads : ∀ {shape} (ref : CStorageRef first shape),
      framed.read (.storage (lift ref)) = original.read (.storage ref))
    {shape : CShape} (input : CInputRef first shape) :
    framed.read (mapInput lift input) = original.read input := by
  induction input with
  | storage ref => exact reads ref
  | product first second firstIH secondIH =>
      exact congrArg₂ CShape.Value.product firstIH secondIH
  | fixedVector entries entriesIH =>
      exact congrArg CShape.Value.fixedVector (funext entriesIH)
  | first source sourceIH => exact congrArg CShape.Value.first sourceIH
  | second source sourceIH => exact congrArg CShape.Value.second sourceIH
  | vectorGet source index sourceIH => exact congrArg (fun value => value.get index) sourceIH
  | bitsGet source index sourceIH => exact congrArg (fun value => value.bitGet index) sourceIH
  | wordBitGet source index sourceIH =>
      exact congrArg (fun value => value.wordBitGet index) sourceIH

variable {kind : ProblemKind} {left right : RuntimeCtx kind}
  (separate : RuntimeCtx.StorageDisjoint left right)

/-- Every lifted structural left read obtains its original value in the actual joined store. -/
lemma contextUnion_read_join_left (first : Store left) (second : Store right)
    {shape : CShape} (input : CInputRef left shape) :
    (join separate first second).read (inputLeft separate input) = first.read input :=
  read_mapInput first (join separate first second) (storageLeft separate)
    (fun ref => read_joinCells_left right.entries first.cells second.cells ref.slot) input

/-- Every structural right read retains its exact original cell value. -/
lemma contextUnion_read_join_right (first : Store left) (second : Store right)
    {shape : CShape} (input : CInputRef right shape) :
    (join separate first second).read (inputRight separate input) = second.read input :=
  read_mapInput second (join separate first second) (storageRight separate)
    (fun ref => read_joinCells_right left.entries first.cells second.cells ref.slot) input

/-- An actual left write changes only the original left store, preserving the entire frame. -/
lemma contextUnion_write_join_left (first : Store left) (second : Store right)
    {shape : CShape} (output : CWriteRef left shape) (value : shape.Value) :
    (join separate first second).write (writeLeft separate output) value =
      join separate (first.write output value) second :=
  congrArg Store.mk
    (write_joinCells_left right.entries first.cells second.cells output.slot value)

/-- An actual right write likewise leaves the entire left store unchanged. -/
lemma contextUnion_write_join_right (first : Store left) (second : Store right)
    {shape : CShape} (output : CWriteRef right shape) (value : shape.Value) :
    (join separate first second).write (writeRight separate output) value =
      join separate first (second.write output value) :=
  congrArg Store.mk
    (write_joinCells_right left.entries first.cells second.cells output.slot value)

end QuantumAlg.Execution.ContextUnion
