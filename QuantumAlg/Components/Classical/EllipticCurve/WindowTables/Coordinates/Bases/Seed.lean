/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Record
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Point
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Row

/-!
# Actual initial coordinates of the small-base arrays

The two real native vector writes copy the actual input words into row
zero. Only the second source must survive the first write. Every other
array row and protected caller read survives, with the original full
chronological record unchanged.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : CoordinateFrame ctx width length)

/-- The complete actual seed record is precisely the two original native overwrites. -/
lemma seedRecord_store (sourceX sourceY : CInputRef ctx (.unsignedWord width)) (row : Fin length)
    (before : Store ctx × model.HiddenState) :
    (frame.seedRecord (model := model) sourceX sourceY row before).1.1 =
      (before.1.applyOp (rowWriteOp frame.x row sourceX)).applyOp
        (rowWriteOp frame.y row sourceY) := rfl

/-- The actual first destination receives the original x input before the real y overwrite. -/
lemma seedRecord_read_x (sourceX sourceY : CInputRef ctx (.unsignedWord width)) (row : Fin length)
    (before : Store ctx × model.HiddenState) :
    (frame.seedRecord (model := model) sourceX sourceY row before).1.1.read (rowRead frame.x row) =
      before.1.read sourceX := by
  rw [frame.seedRecord_store]
  exact (rowWrite_read_array _ _ _ _ _ _ (Ne.symm frame.separate)).trans
    (rowWrite_read_same _ _ _ before.1)

/-- The actual second destination receives the original y input
when the first output is protected. -/
lemma seedRecord_read_y (sourceX sourceY : CInputRef ctx (.unsignedWord width)) (row : Fin length)
    (before : Store ctx × model.HiddenState) (yFree : frame.x.key ∉ sourceY.storageKeys) :
    (frame.seedRecord (model := model) sourceX sourceY row before).1.1.read (rowRead frame.y row) =
      before.1.read sourceY := by
  rw [frame.seedRecord_store]
  exact (rowWrite_read_same _ _ _ _).trans
    (Store.read_applyOp_of_not_mem_storageKeys before.1 (rowWriteOp frame.x row sourceX)
      sourceY yFree)

/-- The same complete actual seed record represents its original supplied finite group point. -/
lemma seedRecord_coordinateValue (curve : CurveSpec width)
    (sourceX sourceY : CInputRef ctx (.unsignedWord width)) (row : Fin length)
    (before : Store ctx × model.HiddenState) (point : Point curve)
    (yFree : frame.x.key ∉ sourceY.storageKeys)
    (input : CoordinateValue curve (before.1.read sourceX) (before.1.read sourceY) point) :
    let returned := (frame.seedRecord (model := model) sourceX sourceY row before).1.1
    CoordinateValue curve (returned.read (rowRead frame.x row))
      (returned.read (rowRead frame.y row)) point := by
  dsimp only
  rw [frame.seedRecord_read_x, frame.seedRecord_read_y sourceX sourceY row before yFree]
  exact input

/-- Every structural caller read outside both actual coordinate outputs survives the two writes. -/
lemma seedRecord_read_other (sourceX sourceY : CInputRef ctx (.unsignedWord width))
    (row : Fin length) (before : Store ctx × model.HiddenState)
    {shape : CShape} (observed : CInputRef ctx shape)
    (xFree : frame.x.key ∉ observed.storageKeys) (yFree : frame.y.key ∉ observed.storageKeys) :
    (frame.seedRecord (model := model) sourceX sourceY row before).1.1.read observed =
      before.1.read observed := by
  rw [frame.seedRecord_store]
  exact (Store.read_applyOp_of_not_mem_storageKeys _ (rowWriteOp frame.y row sourceY)
    observed yFree).trans
      (Store.read_applyOp_of_not_mem_storageKeys before.1 (rowWriteOp frame.x row sourceX)
        observed xFree)

/-- Every unvisited array row survives the exact same complete actual seed record. -/
lemma seedRecord_read_other_row (sourceX sourceY : CInputRef ctx (.unsignedWord width))
    (selected : Fin length) (before : Store ctx × model.HiddenState)
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (row : Fin length) (different : row ≠ selected) :
    (frame.seedRecord (model := model) sourceX sourceY selected before).1.1.read
      (rowRead array row) =
      before.1.read (rowRead array row) := by
  rw [frame.seedRecord_store]
  exact (rowWrite_read_of_row_ne _ _ _ _ _ _ different).trans
    (rowWrite_read_of_row_ne _ _ _ _ _ _ different)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
