/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Result.First
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Result.Last

/-!
# Exact coordinate words before the two original array overwrites

The six real scalar slots preserve the prepared slope while computing
both result coordinates. Their inputs are read from the actual Store at
the block boundary, so no source-coordinate alias is assumed away.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular Field.Native.Shared

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : CoordinateFrame ctx width length)

/-- The actual product word receives precisely the finite-word new x expression. -/
lemma resultStore_read_product (spec : ModulusSpec width) (source : Fin length)
    (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord) :
    (frame.resultStore spec source store).read (wordRead frame.work.product) =
      subValue (multiplyValue (store.read (wordRead frame.work.slope))
        (store.read (wordRead frame.work.slope)) (.unsignedWord spec.extendedWord))
        (addValue (store.read (rowRead frame.x source)) (store.read (rowRead frame.x source))
          (.unsignedWord spec.extendedWord)) (.unsignedWord spec.extendedWord) := by
  rw [frame.resultStore_eq_blocks]
  have retained := frame.resultLastStore_read_other spec source
    (frame.resultFirstStore spec source store) (wordRead frame.work.product) (by
      change frame.work.temporary.key ∉ [frame.work.product.key]
      simpa [Work.word] using frame.work.word_key_ne 2 0 (by decide))
  exact retained.trans (frame.resultFirstStore_read_product spec source store loaded)

/-- The actual temporary word receives precisely the finite-word new y expression. -/
lemma resultStore_read_temporary (spec : ModulusSpec width) (source : Fin length)
    (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord) :
    let modulus : CShape.Word (width + 1) := .unsignedWord spec.extendedWord
    let slope := store.read (wordRead frame.work.slope)
    let nextX := subValue (multiplyValue slope slope modulus)
      (addValue (store.read (rowRead frame.x source)) (store.read (rowRead frame.x source))
        modulus) modulus
    (frame.resultStore spec source store).read (wordRead frame.work.temporary) =
      subValue (multiplyValue slope
        (subValue (store.read (rowRead frame.x source)) nextX modulus) modulus)
        (store.read (rowRead frame.y source)) modulus := by
  let first := frame.resultFirstStore spec source store
  have inputs : InputReads frame source store first :=
    frame.resultFirstStore_inputReads spec source store
  have firstLoaded := inputs.modulus.trans loaded
  rw [frame.resultStore_eq_blocks, frame.resultLastStore_read_temporary spec source first
    firstLoaded, inputs.x, inputs.y, frame.resultFirstStore_read_slope,
    frame.resultFirstStore_read_product spec source store loaded]

/-- The real first destination receives the already-computed original product word. -/
lemma writeStore_read_x (spec : ModulusSpec width) (destination : Fin length)
    (store : Store ctx) :
    (frame.writeStore spec destination store).read (rowRead frame.x destination) =
      store.read (wordRead frame.work.product) := by
  have different := frame.separate
  simp_all [writeStore, RowInstruction.updates, writeInstructions, RowInstruction.update,
    rowWrite_read_array, rowWrite_read_same, eq_comm]

/-- The real second destination receives the original temporary word after the X write. -/
lemma writeStore_read_y (spec : ModulusSpec width) (destination : Fin length)
    (store : Store ctx) :
    (frame.writeStore spec destination store).read (rowRead frame.y destination) =
      store.read (wordRead frame.work.temporary) := by
  have selected : (frame.writeStore spec destination store).read
      (rowRead frame.y destination) =
        (store.applyOp (rowWriteOp frame.x destination (wordRead frame.work.product))).read
          (wordRead frame.work.temporary) := rowWrite_read_same _ _ _ _
  exact selected.trans (rowWrite_read_word _ _ _ _ store)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
