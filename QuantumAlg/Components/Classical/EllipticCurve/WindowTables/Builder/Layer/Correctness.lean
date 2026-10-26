/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Layer.Inversion
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Layer.Extensions

/-!
# Original group values of an actual complete binary layer

The real seed record feeds the real denominator pass, original total
batch inverse and actual secant-extension pass. All original positive
coordinate rows below the next power-of-two frontier therefore represent
their original group multiples, without constraining old working words.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width window : Nat}
  (frame : TableFrame ctx width (2 ^ window))

attribute [local irreducible] prepareSeedRecord layerDenominatorsRecord layerExtensionsRecord
attribute [local irreducible] BatchFrame.valueRecord

/-- Every real binary layer extends the original canonical group-coordinate frontier. -/
lemma layerRecord_rowsValue (curve : CurveSpec width) (level : Fin window)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (point : Point curve) (order : Nat) (prime : order.Prime) (large : 3 < order)
    (original : addOrderOf point = order) (tableFits : 2 ^ window < order)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (one : (before.1.read frame.one).toNat = 1)
    (curveValue : ((before.1.read frame.curveA).toNat : ZMod curve.field.modulus) = curve.curve.a)
    (baseValue : CoordinateValue curve (before.1.read frame.baseX)
      (before.1.read frame.baseY) point)
    (rows : frame.CoordinateRowsValue curve point (2 ^ level.val) before.1) :
    frame.CoordinateRowsValue curve point (2 ^ (level.val + 1))
      (frame.layerRecord curve.field level environment before).1.1 := by
  let seeded := (frame.prepareSeedRecord curve.field level environment before).1
  let denominators := (frame.layerDenominatorsRecord level environment seeded).1
  let inverted := (frame.batch.valueRecord curve.field (layerCount level) (layerFits level)
    environment denominators).1
  have seedInputs := frame.prepareSeedRecord_originalInputs curve.field level environment before
  have denominatorInputs := frame.layerDenominatorsRecord_originalInputs level environment seeded
  have batchInputs := frame.batchRecord_originalInputs curve.field (layerCount level)
    (layerFits level) environment denominators
  have seededLoaded : seeded.1.read (wordRead frame.modulus) =
      .unsignedWord curve.field.extendedWord := seedInputs.modulus.trans loaded
  have denominatorLoaded := denominatorInputs.modulus.trans seededLoaded
  have invertedLoaded := batchInputs.modulus.trans denominatorLoaded
  have seedRows := frame.prepareSeedRecord_rowsValue curve level environment before point order
    prime large original loaded curveValue baseValue rows
  have denominatorRows := frame.layerDenominatorsRecord_rowsValue curve level environment seeded
    point (2 ^ level.val + 1) seedRows
  have invertedRows := frame.batchRecord_rowsValue curve (layerCount level) (layerFits level)
    environment denominators point (2 ^ level.val + 1) denominatorRows
  have xRetained (row : Fin (2 ^ window)) :
      inverted.1.read (rowRead frame.arrays.x row) = seeded.1.read (rowRead frame.arrays.x row) :=
    (frame.batchRecord_read_array_row curve.field (layerCount level) (layerFits level)
      environment denominators frame.arrays.x row
      (by simpa [Arrays.column] using frame.arrays.column_key_ne 2 0 (by decide))
      (by simpa [Arrays.column] using frame.arrays.column_key_ne 3 0 (by decide))).trans
      (frame.layerDenominatorsRecord_read_array_row level environment seeded frame.arrays.x row
        (by simpa [Arrays.column] using frame.arrays.column_key_ne 2 0 (by decide)))
  have orderFits : 2 ^ window < addOrderOf point := by rw [original]; exact tableFits
  change frame.CoordinateRowsValue curve point (2 ^ (level.val + 1))
    (frame.layerExtensionsRecord curve.field level environment inverted).1.1
  apply frame.layerExtensionsRecord_rowsValue curve level environment inverted point orderFits
    invertedLoaded invertedRows
  intro index
  rw [xRetained, xRetained]
  exact frame.layerInvertedRecord_inverse curve level environment seeded point orderFits
    seededLoaded (by rw [seedInputs.inputs frame.one (by simp)]; exact one) seedRows index

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
