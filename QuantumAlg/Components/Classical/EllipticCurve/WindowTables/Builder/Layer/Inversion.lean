/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Layer.Preservation
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Layer.Inputs
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Layer.Domain

/-!
# Exact secant inverses supplied by the actual denominator and C/D batch stages

Every positive old-row denominator is nonzero on the original point-order
domain. The original paid subtractions feed the original total batch
inverse, so its actual returned C words are the inverses required by the
following real secant records. No executable mathematical inverse is added.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve
open Field.Native.Shared

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width window : Nat}
  (frame : TableFrame ctx width (2 ^ window))

/-- Each actual C word after the chronological denominator/batch stages is its secant inverse. -/
lemma layerInvertedRecord_inverse (curve : CurveSpec width) (level : Fin window)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) (point : Point curve)
    (large : 2 ^ window < addOrderOf point)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (one : (before.1.read frame.one).toNat = 1)
    (rows : frame.CoordinateRowsValue curve point (2 ^ level.val + 1) before.1)
    (index : Fin (layerCount level)) :
    let denominators := (frame.layerDenominatorsRecord level environment before).1
    let returned := (frame.batch.valueRecord curve.field (layerCount level) (layerFits level)
      environment denominators).1.1
    ((returned.read (rowRead frame.arrays.c (oldRow level index))).toNat :
      ZMod curve.field.modulus) =
      (((before.1.read (rowRead frame.arrays.x (layerSeed window level))).toNat :
        ZMod curve.field.modulus) -
        (before.1.read (rowRead frame.arrays.x (oldRow level index))).toNat)⁻¹ := by
  let denominators := (frame.layerDenominatorsRecord level environment before).1
  let values : Nat → ZMod curve.field.modulus := fun position =>
    if within : position < layerCount level then
      (before.1.read (rowRead frame.arrays.x (layerSeed window level))).toNat -
        (before.1.read (rowRead frame.arrays.x (oldRow level ⟨position, within⟩))).toNat
    else 0
  have retained := frame.layerDenominatorsRecord_originalInputs level environment before
  have seedValue := rows (layerSeed window level) (Nat.two_pow_pos _) (by
    change 2 ^ level.val < 2 ^ level.val + 1
    omega)
  have oldValue := fun selected : Fin (layerCount level) =>
    rows (oldRow level selected) (layer_old_positive_below_seed level selected).1 (by
      have below := (layer_old_positive_below_seed level selected).2
      change (oldRow level selected).val < 2 ^ level.val at below
      omega)
  have nonzero : ∀ position < layerCount level, values position ≠ 0 := by
    intro position within
    dsimp only [values]
    rw [dif_pos within]
    exact sub_ne_zero.mpr (layer_coordinate_x_ne curve frame level ⟨position, within⟩ before.1
      point large seedValue (oldValue ⟨position, within⟩))
  have represented : ∀ row : Fin (2 ^ window), 1 ≤ row.val → row.val ≤ layerCount level →
      ((denominators.1.read (rowRead frame.arrays.c row)).toNat : ZMod curve.field.modulus) =
        values (row.val - 1) := by
    intro row positive within
    have bound : row.val - 1 < layerCount level := by omega
    let selected : Fin (layerCount level) := ⟨row.val - 1, bound⟩
    have same : oldRow level selected = row := Fin.ext (by
      dsimp only [oldRow, selected]
      omega)
    change (((frame.layerDenominatorsRecord level environment before).1.1.read
      (rowRead frame.arrays.c row)).toNat : ZMod curve.field.modulus) = _
    rw [← same, frame.layerDenominatorsRecord_read_result, loaded]
    have actual := subValue_cast curve.field
      (before.1.read (rowRead frame.arrays.x (layerSeed window level)))
      (before.1.read (rowRead frame.arrays.x (oldRow level selected)))
      (oldValue selected).xCanonical
    simpa only [values, oldRow, selected, Nat.add_sub_cancel, dif_pos bound] using actual
  have actual := frame.batchRecord_denominator_inverse curve.field environment (layerCount level)
    (layerFits level) values denominators (retained.modulus.trans loaded)
    (by rw [retained.inputs frame.one (by simp)]; exact one) nonzero represented
    (oldRow level index) (layer_old_positive_below_seed level index).1 (by
      have bounded := index.isLt
      change index.val + 1 ≤ 2 ^ level.val - 1
      change index.val < 2 ^ level.val - 1 at bounded
      omega)
  have cast := congrArg (fun value : Nat => (value : ZMod curve.field.modulus)) actual
  rw [ZMod.natCast_zmod_val] at cast
  simpa only [values, oldRow, Nat.add_sub_cancel, dif_pos index.isLt] using cast

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
