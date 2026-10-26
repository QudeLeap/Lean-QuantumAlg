/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Finish.Blocks
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Protection
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Framing

/-!
# Exact first-block Store of the final row

The first five original scalar operations prepare the numerator and multiply
by the already-inverted original C entry. Every array and protected caller
input survives those scalar overwrites. Only these five actual slots are
expanded in this proof, sharing the real block boundary Store.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular Field.Native.Shared

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- The exact word-reader alias of the original typed scalar write law. -/
lemma wordWrite_read_same (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) (value : CShape.Word width) :
    (store.write output value).read (wordRead output) = value :=
  Store.read_write_same _ _ _

/-- The literal finite-word numerator built by the original multiply and three additions. -/
def finishNumeratorWord (spec : ModulusSpec width) (x curveA : CShape.Word width) :
    CShape.Word width :=
  let modulus : CShape.Word (width + 1) := .unsignedWord spec.extendedWord
  let square := multiplyValue x x modulus
  addValue (addValue (addValue square square modulus) square modulus) curveA modulus

/-- The first block stores exactly the original numerator times the original C word. -/
lemma finishFirstStore_read_slope (spec : ModulusSpec width) (row : Fin length) (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord) :
    (frame.finishFirstStore spec row store).read (wordRead frame.work.slope) =
      multiplyValue (finishNumeratorWord spec
        (store.read (rowRead frame.arrays.x row)) (store.read frame.curveA))
        (store.read (rowRead frame.arrays.c row)) (.unsignedWord spec.extendedWord) := by
  let modulus := store.read (wordRead frame.modulus)
  let square := multiplyValue (store.read (rowRead frame.arrays.x row))
    (store.read (rowRead frame.arrays.x row)) modulus
  let first := store.write frame.work.temporary square
  let second := first.write frame.work.product
    (addValue (first.read (wordRead frame.work.temporary))
      (first.read (wordRead frame.work.temporary)) (first.read (wordRead frame.modulus)))
  let third := second.write frame.work.product
    (addValue (second.read (wordRead frame.work.product))
      (second.read (wordRead frame.work.temporary)) (second.read (wordRead frame.modulus)))
  let fourth := third.write frame.work.product
    (addValue (third.read (wordRead frame.work.product)) (third.read frame.curveA)
      (third.read (wordRead frame.modulus)))
  have productTemporary : frame.work.product.key ≠ frame.work.temporary.key := by
    have absent := (List.nodup_cons.mp frame.work.distinct).1
    exact fun same => absent (by simp [same])
  have firstTemporary : first.read (wordRead frame.work.temporary) = square :=
    Store.read_write_same _ _ _
  have firstModulus : first.read (wordRead frame.modulus) = modulus :=
    wordWrite_read_modulus _ _ _ _
  have secondProduct : second.read (wordRead frame.work.product) =
      addValue square square modulus := by
    have written : second.read (wordRead frame.work.product) =
        addValue (first.read (wordRead frame.work.temporary))
          (first.read (wordRead frame.work.temporary)) (first.read (wordRead frame.modulus)) :=
      Store.read_write_same _ _ _
    rw [written, firstTemporary, firstModulus]
  have secondTemporary : second.read (wordRead frame.work.temporary) = square :=
    (wordWrite_read_word _ _ _ _ productTemporary).trans firstTemporary
  have secondModulus : second.read (wordRead frame.modulus) = modulus :=
    (wordWrite_read_modulus _ _ _ _).trans firstModulus
  have thirdProduct : third.read (wordRead frame.work.product) =
      addValue (addValue square square modulus) square modulus := by
    have written : third.read (wordRead frame.work.product) =
        addValue (second.read (wordRead frame.work.product))
          (second.read (wordRead frame.work.temporary)) (second.read (wordRead frame.modulus)) :=
      Store.read_write_same _ _ _
    rw [written, secondProduct, secondTemporary, secondModulus]
  have thirdModulus : third.read (wordRead frame.modulus) = modulus :=
    (wordWrite_read_modulus _ _ _ _).trans secondModulus
  have thirdCurve : third.read frame.curveA = store.read frame.curveA :=
    (frame.write_read_curveA _ (by simp [outputKeys]) second _).trans
      ((frame.write_read_curveA _ (by simp [outputKeys]) first _).trans
        (frame.write_read_curveA _ (by simp [outputKeys]) store _))
  have fourthProduct : fourth.read (wordRead frame.work.product) =
      addValue (addValue (addValue square square modulus) square modulus)
        (store.read frame.curveA) modulus := by
    have written : fourth.read (wordRead frame.work.product) =
        addValue (third.read (wordRead frame.work.product)) (third.read frame.curveA)
          (third.read (wordRead frame.modulus)) :=
      Store.read_write_same _ _ _
    rw [written, thirdProduct, thirdCurve, thirdModulus]
  have fourthC : fourth.read (rowRead frame.arrays.c row) =
      store.read (rowRead frame.arrays.c row) :=
    (wordWrite_read_row _ _ _ third _).trans
      ((wordWrite_read_row _ _ _ second _).trans
        ((wordWrite_read_row _ _ _ first _).trans (wordWrite_read_row _ _ _ store _)))
  have fourthModulus : fourth.read (wordRead frame.modulus) = modulus :=
    (wordWrite_read_modulus _ _ _ _).trans thirdModulus
  change (fourth.write frame.work.slope
    (multiplyValue (fourth.read (wordRead frame.work.product))
      (fourth.read (rowRead frame.arrays.c row))
      (fourth.read (wordRead frame.modulus)))).read (wordRead frame.work.slope) = _
  have written : (fourth.write frame.work.slope
      (multiplyValue (fourth.read (wordRead frame.work.product))
        (fourth.read (rowRead frame.arrays.c row))
        (fourth.read (wordRead frame.modulus)))).read (wordRead frame.work.slope) =
      multiplyValue (fourth.read (wordRead frame.work.product))
        (fourth.read (rowRead frame.arrays.c row)) (fourth.read (wordRead frame.modulus)) :=
    Store.read_write_same _ _ _
  rw [written, fourthProduct, fourthC, fourthModulus]
  dsimp only [square, modulus]
  rw [loaded]
  rfl

/-- No array or protected structural read changes beyond the three actual scalar outputs. -/
lemma finishFirstStore_read_other (spec : ModulusSpec width) (row : Fin length)
    (store : Store ctx) {shape : CShape} (observed : CInputRef ctx shape)
    (productFree : frame.work.product.key ∉ observed.storageKeys)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys)
    (slopeFree : frame.work.slope.key ∉ observed.storageKeys) :
    (frame.finishFirstStore spec row store).read observed = store.read observed := by
  apply RowInstruction.updates_read_other
  intro index
  fin_cases index <;> first | exact temporaryFree | exact productFree | exact slopeFree

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
