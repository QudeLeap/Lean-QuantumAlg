/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Result.Blocks

/-!
# Exact new-y scalar at the original three-slot boundary

The same temporary word is overwritten three times. The preserved prepared
slope, actual new-x product and original coordinate inputs determine its
final value before either destination array is changed.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular Field.Native.Shared

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : CoordinateFrame ctx width length)

/-- The last three actual scalar slots compute the original new-y finite expression. -/
lemma resultLastStore_read_temporary (spec : ModulusSpec width) (source : Fin length)
    (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord) :
    (frame.resultLastStore spec source store).read (wordRead frame.work.temporary) =
      subValue (multiplyValue (store.read (wordRead frame.work.slope))
        (subValue (store.read (rowRead frame.x source)) (store.read (wordRead frame.work.product))
          (.unsignedWord spec.extendedWord)) (.unsignedWord spec.extendedWord))
        (store.read (rowRead frame.y source)) (.unsignedWord spec.extendedWord) := by
  let modulus := store.read (wordRead frame.modulus)
  let difference := subValue (store.read (rowRead frame.x source))
    (store.read (wordRead frame.work.product)) modulus
  let first := store.write frame.work.temporary difference
  let second := first.write frame.work.temporary
    (multiplyValue (first.read (wordRead frame.work.slope))
      (first.read (wordRead frame.work.temporary)) (first.read (wordRead frame.modulus)))
  have firstTemporary : first.read (wordRead frame.work.temporary) = difference :=
    Store.read_write_same _ _ _
  have firstSlope : first.read (wordRead frame.work.slope) =
      store.read (wordRead frame.work.slope) :=
    wordWrite_read_word _ _ store _ (frame.work.word_key_ne 2 3 (by decide))
  have firstModulus : first.read (wordRead frame.modulus) = modulus :=
    wordWrite_read_modulus _ _ store _
  have secondTemporary : second.read (wordRead frame.work.temporary) =
      multiplyValue (first.read (wordRead frame.work.slope))
        (first.read (wordRead frame.work.temporary)) (first.read (wordRead frame.modulus)) :=
    Store.read_write_same _ _ _
  have secondY : second.read (rowRead frame.y source) = store.read (rowRead frame.y source) :=
    (wordWrite_read_row _ _ _ first _).trans (wordWrite_read_row _ _ _ store _)
  have secondModulus : second.read (wordRead frame.modulus) = modulus :=
    (wordWrite_read_modulus _ _ first _).trans firstModulus
  change (second.write frame.work.temporary
    (subValue (second.read (wordRead frame.work.temporary))
      (second.read (rowRead frame.y source))
      (second.read (wordRead frame.modulus)))).read (wordRead frame.work.temporary) = _
  rw [TableFrame.wordWrite_read_same, secondTemporary, secondY, secondModulus,
    firstSlope, firstTemporary, firstModulus]
  dsimp only [difference, modulus]
  rw [loaded]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
