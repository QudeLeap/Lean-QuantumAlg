/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Result.Blocks

/-!
# Exact new-x scalar at the original three-slot boundary

The original two-x word is retained while the square of the prepared
slope is computed. The actual subtraction writes the new x to the same
product word, with every coordinate input and slope read preserved.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular Field.Native.Shared

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : CoordinateFrame ctx width length)

/-- Both original coordinates and supplied inputs survive the first three result slots. -/
lemma resultFirstStore_inputReads (spec : ModulusSpec width) (source : Fin length)
    (store : Store ctx) :
    InputReads frame source store (frame.resultFirstStore spec source store) := by
  constructor
  · exact frame.resultFirstStore_read_other spec source store _
      (frame.scalar_modulus_free _) (frame.scalar_modulus_free _)
  · exact frame.resultFirstStore_read_other spec source store _
      (scalar_row_free _ _ _) (scalar_row_free _ _ _)
  · exact frame.resultFirstStore_read_other spec source store _
      (scalar_row_free _ _ _) (scalar_row_free _ _ _)
  · apply frame.resultFirstStore_read_other
    all_goals exact frame.protectedCoefficient _ (by simp)

/-- The original prepared slope survives all three first-half writes exactly. -/
lemma resultFirstStore_read_slope (spec : ModulusSpec width) (source : Fin length)
    (store : Store ctx) :
    (frame.resultFirstStore spec source store).read (wordRead frame.work.slope) =
      store.read (wordRead frame.work.slope) := by
  apply frame.resultFirstStore_read_other
  · change frame.work.product.key ∉ [frame.work.slope.key]
    simpa [Work.word] using frame.work.word_key_ne 0 3 (by decide)
  · change frame.work.temporary.key ∉ [frame.work.slope.key]
    simpa [Work.word] using frame.work.word_key_ne 2 3 (by decide)

/-- The actual three-slot product word is exactly the original new-x finite expression. -/
lemma resultFirstStore_read_product (spec : ModulusSpec width) (source : Fin length)
    (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord) :
    (frame.resultFirstStore spec source store).read (wordRead frame.work.product) =
      subValue (multiplyValue (store.read (wordRead frame.work.slope))
        (store.read (wordRead frame.work.slope)) (.unsignedWord spec.extendedWord))
        (addValue (store.read (rowRead frame.x source)) (store.read (rowRead frame.x source))
          (.unsignedWord spec.extendedWord)) (.unsignedWord spec.extendedWord) := by
  let modulus := store.read (wordRead frame.modulus)
  let doubled := addValue (store.read (rowRead frame.x source))
    (store.read (rowRead frame.x source)) modulus
  let first := store.write frame.work.product doubled
  let second := first.write frame.work.temporary
    (multiplyValue (first.read (wordRead frame.work.slope))
      (first.read (wordRead frame.work.slope)) (first.read (wordRead frame.modulus)))
  have firstProduct : first.read (wordRead frame.work.product) = doubled :=
    Store.read_write_same _ _ _
  have firstSlope : first.read (wordRead frame.work.slope) =
      store.read (wordRead frame.work.slope) :=
    wordWrite_read_word _ _ store _ (frame.work.word_key_ne 0 3 (by decide))
  have firstModulus : first.read (wordRead frame.modulus) = modulus :=
    wordWrite_read_modulus _ _ store _
  have secondTemporary : second.read (wordRead frame.work.temporary) =
      multiplyValue (first.read (wordRead frame.work.slope))
        (first.read (wordRead frame.work.slope)) (first.read (wordRead frame.modulus)) :=
    Store.read_write_same _ _ _
  have secondProduct : second.read (wordRead frame.work.product) = doubled :=
    (wordWrite_read_word _ _ first _ (frame.work.word_key_ne 2 0 (by decide))).trans firstProduct
  have secondModulus : second.read (wordRead frame.modulus) = modulus :=
    (wordWrite_read_modulus _ _ first _).trans firstModulus
  change (second.write frame.work.product
    (subValue (second.read (wordRead frame.work.temporary))
      (second.read (wordRead frame.work.product))
      (second.read (wordRead frame.modulus)))).read (wordRead frame.work.product) = _
  rw [TableFrame.wordWrite_read_same, secondTemporary, secondProduct, secondModulus,
    firstSlope, firstModulus]
  dsimp only [doubled, modulus]
  rw [loaded]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
