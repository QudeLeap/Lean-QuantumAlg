/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Finish.Middle

/-!
# Exact terminal-block Store of the final row

The last five original slots copy the prepared x+1 word to E, then negate
and overwrite X/Y. The zero input remains its actual protected stored word.
The original C/D columns and every other protected read remain unchanged.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular Field.Native.Shared

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

private lemma x_ne_y : frame.arrays.x.key ≠ frame.arrays.y.key := by
  have absent := (List.nodup_cons.mp frame.arrays.distinct).1
  exact fun same => absent (by simp [same])

private lemma x_ne_e : frame.arrays.x.key ≠ frame.arrays.e.key := by
  have absent := (List.nodup_cons.mp frame.arrays.distinct).1
  exact fun same => absent (by simp [same])

private lemma y_ne_e : frame.arrays.y.key ≠ frame.arrays.e.key := by
  have absent := (List.nodup_cons.mp (List.nodup_cons.mp frame.arrays.distinct).2).1
  exact fun same => absent (by simp [same])

private lemma rowWrite_read_zero
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (row : Fin length) (input : CInputRef ctx (.unsignedWord width))
    (inside : array.key ∈ frame.outputKeys) (store : Store ctx) :
    (store.applyOp (rowWriteOp array row input)).read frame.zero = store.read frame.zero :=
  frame.applyOp_read_zero (rowWriteOp array row input) inside store

/-- The real E overwrite receives the preceding actual prepared temporary word. -/
lemma finishLastStore_read_e (spec : ModulusSpec width) (row : Fin length) (store : Store ctx) :
    (frame.finishLastStore spec row store).read (rowRead frame.arrays.e row) =
      store.read (wordRead frame.work.temporary) := by
  have xe := frame.x_ne_e
  have ye := frame.y_ne_e
  simp_all [finishLastStore, RowInstruction.updates, finishLastInstructions,
    RowInstruction.update, wordWrite_read_row, rowWrite_read_array, rowWrite_read_same, eq_comm]

/-- The real X overwrite receives the negative original x expression with its actual zero word. -/
lemma finishLastStore_read_x (spec : ModulusSpec width) (row : Fin length) (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord) :
    (frame.finishLastStore spec row store).read (rowRead frame.arrays.x row) =
      subValue (store.read frame.zero) (store.read (rowRead frame.arrays.x row))
        (.unsignedWord spec.extendedWord) := by
  let first := store.applyOp (rowWriteOp frame.arrays.e row (wordRead frame.work.temporary))
  let second := first.write frame.work.temporary
    (subValue (first.read frame.zero) (first.read (rowRead frame.arrays.x row))
      (first.read (wordRead frame.modulus)))
  let third := second.applyOp (rowWriteOp frame.arrays.x row (wordRead frame.work.temporary))
  let fourth := third.write frame.work.temporary
    (subValue (third.read frame.zero) (third.read (rowRead frame.arrays.y row))
      (third.read (wordRead frame.modulus)))
  have firstZero : first.read frame.zero = store.read frame.zero :=
    frame.rowWrite_read_zero _ _ _ (by simp [outputKeys]) store
  have firstX : first.read (rowRead frame.arrays.x row) =
      store.read (rowRead frame.arrays.x row) :=
    rowWrite_read_array _ _ _ _ _ store (Ne.symm frame.x_ne_e)
  have firstModulus : first.read (wordRead frame.modulus) =
      store.read (wordRead frame.modulus) := rowWrite_read_modulus _ _ _ _ store
  have secondTemporary : second.read (wordRead frame.work.temporary) =
      subValue (first.read frame.zero) (first.read (rowRead frame.arrays.x row))
        (first.read (wordRead frame.modulus)) := Store.read_write_same _ _ _
  have finalX : (frame.finishLastStore spec row store).read (rowRead frame.arrays.x row) =
      second.read (wordRead frame.work.temporary) :=
    (rowWrite_read_array _ _ _ _ _ fourth (Ne.symm frame.x_ne_y)).trans
      ((wordWrite_read_row _ _ _ third _).trans (rowWrite_read_same _ _ _ second))
  rw [finalX, secondTemporary, firstZero, firstX, firstModulus, loaded]

/-- The real Y overwrite receives the negative original y expression after the actual X write. -/
lemma finishLastStore_read_y (spec : ModulusSpec width) (row : Fin length) (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord) :
    (frame.finishLastStore spec row store).read (rowRead frame.arrays.y row) =
      subValue (store.read frame.zero) (store.read (rowRead frame.arrays.y row))
        (.unsignedWord spec.extendedWord) := by
  let first := store.applyOp (rowWriteOp frame.arrays.e row (wordRead frame.work.temporary))
  let second := first.write frame.work.temporary
    (subValue (first.read frame.zero) (first.read (rowRead frame.arrays.x row))
      (first.read (wordRead frame.modulus)))
  let third := second.applyOp (rowWriteOp frame.arrays.x row (wordRead frame.work.temporary))
  let fourth := third.write frame.work.temporary
    (subValue (third.read frame.zero) (third.read (rowRead frame.arrays.y row))
      (third.read (wordRead frame.modulus)))
  have thirdZero : third.read frame.zero = store.read frame.zero :=
    (frame.rowWrite_read_zero _ _ _ (by simp [outputKeys]) second).trans
      ((frame.write_read_zero _ (by simp [outputKeys]) first _).trans
        (frame.rowWrite_read_zero _ _ _ (by simp [outputKeys]) store))
  have thirdY : third.read (rowRead frame.arrays.y row) =
      store.read (rowRead frame.arrays.y row) :=
    (rowWrite_read_array _ _ _ _ _ second frame.x_ne_y).trans
      ((wordWrite_read_row _ _ _ first _).trans
        (rowWrite_read_array _ _ _ _ _ store (Ne.symm frame.y_ne_e)))
  have thirdModulus : third.read (wordRead frame.modulus) =
      store.read (wordRead frame.modulus) :=
    (rowWrite_read_modulus _ _ _ _ second).trans
      ((wordWrite_read_modulus _ _ first _).trans (rowWrite_read_modulus _ _ _ _ store))
  have fourthTemporary : fourth.read (wordRead frame.work.temporary) =
      subValue (third.read frame.zero) (third.read (rowRead frame.arrays.y row))
        (third.read (wordRead frame.modulus)) := Store.read_write_same _ _ _
  have finalY : (frame.finishLastStore spec row store).read (rowRead frame.arrays.y row) =
      fourth.read (wordRead frame.work.temporary) := rowWrite_read_same _ _ _ fourth
  rw [finalY, fourthTemporary, thirdZero, thirdY, thirdModulus, loaded]

/-- Reads outside the three terminal columns and temporary word survive the actual last block. -/
lemma finishLastStore_read_other (spec : ModulusSpec width) (row : Fin length)
    (store : Store ctx) {shape : CShape} (observed : CInputRef ctx shape)
    (eFree : frame.arrays.e.key ∉ observed.storageKeys)
    (xFree : frame.arrays.x.key ∉ observed.storageKeys)
    (yFree : frame.arrays.y.key ∉ observed.storageKeys)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys) :
    (frame.finishLastStore spec row store).read observed = store.read observed := by
  apply RowInstruction.updates_read_other
  intro index
  fin_cases index <;> first | exact eFree | exact xFree | exact yFree | exact temporaryFree

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
