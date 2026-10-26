/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Result
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Values

/-!
# Exact result Store of actual two-array doubling

Both coordinates come from the original input row and original supplied
curve coefficient. The same paid raw coefficient and fifteen actual slots
give these outputs, including when the destination is the input row. The
complete chronological record retains arbitrary incoming history/reference.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular Field.Native.Shared

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : CoordinateFrame ctx width length)

/-- Both real destination columns contain precisely the original finite-word doubling pair. -/
lemma doubleStore_read_values (spec : ModulusSpec width) (source destination : Fin length)
    (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord) :
    let values := doubleWords spec (store.read (rowRead frame.x source))
      (store.read (rowRead frame.y source)) (store.read frame.curveA)
    (frame.doubleStore spec source destination store).read (rowRead frame.x destination) =
        values.1 ∧
      (frame.doubleStore spec source destination store).read (rowRead frame.y destination) =
        values.2 := by
  let prepared := frame.slopeStore spec source store
  have inputs : InputReads frame source store prepared :=
    frame.slopeStore_inputReads spec source store
  have preparedLoaded := inputs.modulus.trans loaded
  have slope := frame.slopeStore_read_slope spec source store loaded
  constructor
  · rw [frame.doubleStore_eq_blocks, frame.writeStore_read_x,
      frame.resultStore_read_product spec source prepared preparedLoaded]
    rw [inputs.x, slope]
    rfl
  · rw [frame.doubleStore_eq_blocks, frame.writeStore_read_y,
      frame.resultStore_read_temporary spec source prepared preparedLoaded]
    rw [inputs.x, inputs.y, slope]
    rfl

/-- An arbitrary structural read outside the actual six caller outputs survives all slots. -/
lemma doubleStore_read_other (spec : ModulusSpec width) (source destination : Fin length)
    (store : Store ctx) {shape : CShape} (observed : CInputRef ctx shape)
    (xFree : frame.x.key ∉ observed.storageKeys) (yFree : frame.y.key ∉ observed.storageKeys)
    (productFree : frame.work.product.key ∉ observed.storageKeys)
    (inverseFree : frame.work.inverse.key ∉ observed.storageKeys)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys)
    (slopeFree : frame.work.slope.key ∉ observed.storageKeys) :
    (frame.doubleStore spec source destination store).read observed = store.read observed := by
  apply RowInstruction.updates_read_other
  intro index
  fin_cases index <;>
    first | exact xFree | exact yFree | exact productFree | exact inverseFree |
      exact temporaryFree | exact slopeFree

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  (frame : CoordinateFrame ctx width length)

/-- The Store in the actual full-history record is exactly this same total finite-word Store. -/
lemma doubleRecord_store (spec : ModulusSpec width) (source destination : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    (frame.doubleRecord spec source destination environment before).1.1 =
      frame.doubleStore spec source destination before.1 :=
  RowInstruction.rangeRecord_store spec frame.modulus environment 15
    (frame.instructions source destination) before

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
