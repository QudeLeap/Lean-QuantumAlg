/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Observation
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Words
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Finish.First

/-!
# Exact slope word of the actual seven-slot doubling prefix

The proof follows the real intermediate Stores. The paid raw coefficient
reads the actual two-y word before the product word is reused for the
numerator. No condition is imposed on any old working-word contents.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular Field.Native.Shared

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : CoordinateFrame ctx width length)

/-- The real slope prefix gives the original finite-word numerator times its paid coefficient. -/
lemma slopeStore_read_slope (spec : ModulusSpec width) (source : Fin length) (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord) :
    (frame.slopeStore spec source store).read (wordRead frame.work.slope) =
      multiplyValue (TableFrame.finishNumeratorWord spec
        (store.read (rowRead frame.x source)) (store.read frame.curveA))
        (coefficientWordValue spec
          (addValue (store.read (rowRead frame.y source)) (store.read (rowRead frame.y source))
            (.unsignedWord spec.extendedWord))) (.unsignedWord spec.extendedWord) := by
  let modulus := store.read (wordRead frame.modulus)
  let denominator := addValue (store.read (rowRead frame.y source))
    (store.read (rowRead frame.y source)) modulus
  let inverse := coefficientWordValue spec denominator
  let square := multiplyValue (store.read (rowRead frame.x source))
    (store.read (rowRead frame.x source)) modulus
  let first := store.write frame.work.product denominator
  let second := first.write frame.work.inverse
    (coefficientWordValue spec (first.read (wordRead frame.work.product)))
  let third := second.write frame.work.temporary
    (multiplyValue (second.read (rowRead frame.x source))
      (second.read (rowRead frame.x source)) (second.read (wordRead frame.modulus)))
  let fourth := third.write frame.work.product
    (addValue (third.read (wordRead frame.work.temporary))
      (third.read (wordRead frame.work.temporary)) (third.read (wordRead frame.modulus)))
  let fifth := fourth.write frame.work.product
    (addValue (fourth.read (wordRead frame.work.product))
      (fourth.read (wordRead frame.work.temporary)) (fourth.read (wordRead frame.modulus)))
  let sixth := fifth.write frame.work.product
    (addValue (fifth.read (wordRead frame.work.product)) (fifth.read frame.curveA)
      (fifth.read (wordRead frame.modulus)))
  have productInverse := frame.work.word_key_ne 0 1 (by decide)
  have pt := frame.work.word_key_ne 0 2 (by decide)
  have ti := frame.work.word_key_ne 2 1 (by decide)
  have firstProduct : first.read (wordRead frame.work.product) = denominator :=
    Store.read_write_same _ _ _
  have secondInverse : second.read (wordRead frame.work.inverse) = inverse := by
    have written : second.read (wordRead frame.work.inverse) =
        coefficientWordValue spec (first.read (wordRead frame.work.product)) :=
      Store.read_write_same _ _ _
    rw [written, firstProduct]
  have secondX : second.read (rowRead frame.x source) = store.read (rowRead frame.x source) :=
    (wordWrite_read_row _ _ _ first _).trans (wordWrite_read_row _ _ _ store _)
  have secondModulus : second.read (wordRead frame.modulus) = modulus :=
    (wordWrite_read_modulus _ _ first _).trans (wordWrite_read_modulus _ _ store _)
  have thirdTemporary : third.read (wordRead frame.work.temporary) = square := by
    have written : third.read (wordRead frame.work.temporary) =
        multiplyValue (second.read (rowRead frame.x source))
          (second.read (rowRead frame.x source)) (second.read (wordRead frame.modulus)) :=
      Store.read_write_same _ _ _
    rw [written, secondX, secondModulus]
  have thirdInverse : third.read (wordRead frame.work.inverse) = inverse :=
    (wordWrite_read_word _ _ second _ ti).trans secondInverse
  have thirdModulus : third.read (wordRead frame.modulus) = modulus :=
    (wordWrite_read_modulus _ _ second _).trans secondModulus
  have fourthProduct : fourth.read (wordRead frame.work.product) =
      addValue square square modulus := by
    have written : fourth.read (wordRead frame.work.product) =
        addValue (third.read (wordRead frame.work.temporary))
          (third.read (wordRead frame.work.temporary)) (third.read (wordRead frame.modulus)) :=
      Store.read_write_same _ _ _
    rw [written, thirdTemporary, thirdModulus]
  have fourthTemporary : fourth.read (wordRead frame.work.temporary) = square :=
    (wordWrite_read_word _ _ third _ pt).trans thirdTemporary
  have fourthInverse : fourth.read (wordRead frame.work.inverse) = inverse :=
    (wordWrite_read_word _ _ third _ productInverse).trans thirdInverse
  have fourthModulus : fourth.read (wordRead frame.modulus) = modulus :=
    (wordWrite_read_modulus _ _ third _).trans thirdModulus
  have fifthProduct : fifth.read (wordRead frame.work.product) =
      addValue (addValue square square modulus) square modulus := by
    have written : fifth.read (wordRead frame.work.product) =
        addValue (fourth.read (wordRead frame.work.product))
          (fourth.read (wordRead frame.work.temporary)) (fourth.read (wordRead frame.modulus)) :=
      Store.read_write_same _ _ _
    rw [written, fourthProduct, fourthTemporary, fourthModulus]
  have fifthInverse : fifth.read (wordRead frame.work.inverse) = inverse :=
    (wordWrite_read_word _ _ fourth _ productInverse).trans fourthInverse
  have fifthModulus : fifth.read (wordRead frame.modulus) = modulus :=
    (wordWrite_read_modulus _ _ fourth _).trans fourthModulus
  have fifthCurve : fifth.read frame.curveA = store.read frame.curveA :=
    (frame.write_read_curveA 0 fourth _).trans
      ((frame.write_read_curveA 0 third _).trans
        ((frame.write_read_curveA 2 second _).trans
          ((frame.write_read_curveA 1 first _).trans (frame.write_read_curveA 0 store _))))
  have sixthProduct : sixth.read (wordRead frame.work.product) =
      addValue (addValue (addValue square square modulus) square modulus)
        (store.read frame.curveA) modulus := by
    have written : sixth.read (wordRead frame.work.product) =
        addValue (fifth.read (wordRead frame.work.product)) (fifth.read frame.curveA)
          (fifth.read (wordRead frame.modulus)) := Store.read_write_same _ _ _
    rw [written, fifthProduct, fifthCurve, fifthModulus]
  have sixthInverse : sixth.read (wordRead frame.work.inverse) = inverse :=
    (wordWrite_read_word _ _ fifth _ productInverse).trans fifthInverse
  have sixthModulus : sixth.read (wordRead frame.modulus) = modulus :=
    (wordWrite_read_modulus _ _ fifth _).trans fifthModulus
  change (sixth.write frame.work.slope
    (multiplyValue (sixth.read (wordRead frame.work.product))
      (sixth.read (wordRead frame.work.inverse))
      (sixth.read (wordRead frame.modulus)))).read (wordRead frame.work.slope) = _
  rw [TableFrame.wordWrite_read_same, sixthProduct, sixthInverse, sixthModulus]
  dsimp only [square, inverse, denominator, modulus]
  rw [loaded]
  rfl

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
