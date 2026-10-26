/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Finish.First

/-!
# Exact middle-block Store of the final row

The next original five slots write the prepared slope to D, write 3x to C
and prepare x+1 in the existing temporary word. X/Y and protected supplied
inputs retain their original values. No additional array is allocated.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular Field.Native.Shared

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

private lemma x_ne_c : frame.arrays.x.key ≠ frame.arrays.c.key := by
  have absent := (List.nodup_cons.mp frame.arrays.distinct).1
  exact fun same => absent (by simp [same])

private lemma x_ne_d : frame.arrays.x.key ≠ frame.arrays.d.key := by
  have absent := (List.nodup_cons.mp frame.arrays.distinct).1
  exact fun same => absent (by simp [same])

private lemma c_ne_d : frame.arrays.c.key ≠ frame.arrays.d.key := by
  have absent := (List.nodup_cons.mp
    (List.nodup_cons.mp (List.nodup_cons.mp frame.arrays.distinct).2).2).1
  exact fun same => absent (by simp [same])

/-- D receives precisely the original prepared slope, before any scalar reuse. -/
lemma finishMiddleStore_read_d (spec : ModulusSpec width) (row : Fin length) (store : Store ctx) :
    (frame.finishMiddleStore spec row store).read (rowRead frame.arrays.d row) =
      store.read (wordRead frame.work.slope) := by
  have different := frame.c_ne_d
  simp_all [finishMiddleStore, RowInstruction.updates, finishMiddleInstructions,
    RowInstruction.update, wordWrite_read_same, wordWrite_read_row, rowWrite_read_array,
    rowWrite_read_same]

/-- C receives exactly the original finite-word three-x expression. -/
lemma finishMiddleStore_read_c (spec : ModulusSpec width) (row : Fin length) (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord) :
    (frame.finishMiddleStore spec row store).read (rowRead frame.arrays.c row) =
      addValue (addValue (store.read (rowRead frame.arrays.x row))
        (store.read (rowRead frame.arrays.x row)) (.unsignedWord spec.extendedWord))
        (store.read (rowRead frame.arrays.x row)) (.unsignedWord spec.extendedWord) := by
  have xd := frame.x_ne_d
  have xc := frame.x_ne_c
  simp_all [finishMiddleStore, RowInstruction.updates, finishMiddleInstructions,
    RowInstruction.update, wordWrite_read_same, wordWrite_read_row, wordWrite_read_modulus,
    rowWrite_read_array, rowWrite_read_same, rowWrite_read_modulus, eq_comm]

/-- The existing temporary word receives the original x plus the actual supplied one word. -/
lemma finishMiddleStore_read_temporary (spec : ModulusSpec width) (row : Fin length)
    (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord) :
    (frame.finishMiddleStore spec row store).read (wordRead frame.work.temporary) =
      addValue (store.read (rowRead frame.arrays.x row)) (store.read frame.one)
        (.unsignedWord spec.extendedWord) := by
  let first := store.applyOp (rowWriteOp frame.arrays.d row (wordRead frame.work.slope))
  let second := first.write frame.work.temporary
    (addValue (first.read (rowRead frame.arrays.x row))
      (first.read (rowRead frame.arrays.x row)) (first.read (wordRead frame.modulus)))
  let third := second.write frame.work.temporary
    (addValue (second.read (wordRead frame.work.temporary))
      (second.read (rowRead frame.arrays.x row)) (second.read (wordRead frame.modulus)))
  let fourth := third.applyOp (rowWriteOp frame.arrays.c row (wordRead frame.work.temporary))
  have originalX : fourth.read (rowRead frame.arrays.x row) =
      store.read (rowRead frame.arrays.x row) :=
    (rowWrite_read_array _ _ _ _ _ third (Ne.symm frame.x_ne_c)).trans
      ((wordWrite_read_row _ _ _ second _).trans
        ((wordWrite_read_row _ _ _ first _).trans
          (rowWrite_read_array _ _ _ _ _ store (Ne.symm frame.x_ne_d))))
  have originalOne : fourth.read frame.one = store.read frame.one :=
    (frame.applyOp_read_one (rowWriteOp frame.arrays.c row (wordRead frame.work.temporary))
      (by change frame.arrays.c.key ∈ frame.outputKeys; simp [outputKeys]) third).trans
      ((frame.write_read_one _ (by simp [outputKeys]) second _).trans
        ((frame.write_read_one _ (by simp [outputKeys]) first _).trans
          (frame.applyOp_read_one (rowWriteOp frame.arrays.d row (wordRead frame.work.slope))
            (by change frame.arrays.d.key ∈ frame.outputKeys; simp [outputKeys]) store)))
  have originalModulus : fourth.read (wordRead frame.modulus) =
      store.read (wordRead frame.modulus) :=
    (rowWrite_read_modulus _ _ _ _ third).trans
      ((wordWrite_read_modulus _ _ second _).trans
        ((wordWrite_read_modulus _ _ first _).trans (rowWrite_read_modulus _ _ _ _ store)))
  change (fourth.write frame.work.temporary
    (addValue (fourth.read (rowRead frame.arrays.x row)) (fourth.read frame.one)
      (fourth.read (wordRead frame.modulus)))).read (wordRead frame.work.temporary) = _
  rw [wordWrite_read_same, originalX, originalOne, originalModulus, loaded]

/-- Every structural read outside D, C and the temporary word survives the middle block. -/
lemma finishMiddleStore_read_other (spec : ModulusSpec width) (row : Fin length)
    (store : Store ctx) {shape : CShape} (observed : CInputRef ctx shape)
    (dFree : frame.arrays.d.key ∉ observed.storageKeys)
    (cFree : frame.arrays.c.key ∉ observed.storageKeys)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys) :
    (frame.finishMiddleStore spec row store).read observed = store.read observed := by
  apply RowInstruction.updates_read_other
  intro index
  fin_cases index <;> first | exact dFree | exact cFree | exact temporaryFree

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
