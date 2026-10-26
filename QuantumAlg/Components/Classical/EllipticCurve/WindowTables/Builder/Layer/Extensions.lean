/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Layer.Coordinates
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Layer.Domain
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Layer.Record
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Inputs.Rows
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Extend.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Extend.Preservation
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.Columns
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Invariant

/-!
# Original group values through the actual secant-extension pass

The real batch output supplies every inverse C word. Each ten-slot secant
record reads the actual retained seed and earlier row, writes only its
original new coordinate row, and preserves all previously constructed
rows. The chronological pass doubles the natural construction frontier.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width window : Nat}
  (frame : TableFrame ctx width (2 ^ window))

private lemma extendRecord_read_inverse (spec : ModulusSpec width)
    (seed source destination : Fin (2 ^ window)) (environment : model.Environment)
    (before : Store ctx × model.HiddenState) (row : Fin (2 ^ window)) :
    (frame.extendRecord spec seed source destination environment before).1.1.read
      (rowRead frame.arrays.c row) = before.1.read (rowRead frame.arrays.c row) := by
  rw [frame.extendRecord_store]
  apply frame.extendStore_read_other
  · change frame.work.temporary.key ∉ [frame.arrays.c.key]
    simpa only [List.mem_singleton] using word_array_key_ne _ _
  · change frame.work.slope.key ∉ [frame.arrays.c.key]
    simpa only [List.mem_singleton] using word_array_key_ne _ _
  · change frame.work.product.key ∉ [frame.arrays.c.key]
    simpa only [List.mem_singleton] using word_array_key_ne _ _
  · change frame.arrays.x.key ∉ [frame.arrays.c.key]
    simpa [Arrays.column] using frame.arrays.column_key_ne 0 2 (by decide)
  · change frame.arrays.y.key ∉ [frame.arrays.c.key]
    simpa [Arrays.column] using frame.arrays.column_key_ne 1 2 (by decide)

/-- The original pass constructs every new multiple from the real retained batch inverse words. -/
lemma layerExtensionsRecord_rowsValue (curve : CurveSpec width) (level : Fin window)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) (point : Point curve)
    (large : 2 ^ window < addOrderOf point)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (rows : frame.CoordinateRowsValue curve point (2 ^ level.val + 1) before.1)
    (inverse : ∀ index : Fin (layerCount level),
      ((before.1.read (rowRead frame.arrays.c (oldRow level index))).toNat :
        ZMod curve.field.modulus) =
        (((before.1.read (rowRead frame.arrays.x (layerSeed window level))).toNat :
          ZMod curve.field.modulus) -
          (before.1.read (rowRead frame.arrays.x (oldRow level index))).toNat)⁻¹) :
    frame.CoordinateRowsValue curve point (2 ^ (level.val + 1))
      (frame.layerExtensionsRecord curve.field level environment before).1.1 := by
  let invariant := fun processed (current : Store ctx × model.HiddenState) =>
    OriginalInputs frame before.1 current.1 ∧
      (∀ row : Fin (2 ^ window), row.val ≤ 2 ^ level.val →
        current.1.read (rowRead frame.arrays.x row) = before.1.read (rowRead frame.arrays.x row) ∧
        current.1.read (rowRead frame.arrays.y row) = before.1.read (rowRead frame.arrays.y row)) ∧
      (∀ row, current.1.read (rowRead frame.arrays.c row) =
        before.1.read (rowRead frame.arrays.c row)) ∧
      frame.CoordinateRowsValue curve point (2 ^ level.val + processed + 1) current.1
  have completed := Circuit.forRangeRecord_invariant (layerCount level)
    (fun index => frame.extendRow (layerSeed window level) (oldRow level index)
      (newRow level index))
    (fun index => frame.extendRecord curve.field (layerSeed window level) (oldRow level index)
      (newRow level index) environment)
    invariant (fun index current established => by
      have oldBounds := layer_old_positive_below_seed level index
      have currentOld := established.2.2.2 (oldRow level index) oldBounds.1 (by
        have oldBelow := oldBounds.2
        change (oldRow level index).val < 2 ^ level.val at oldBelow
        omega)
      have currentSeed := established.2.2.2 (layerSeed window level) (Nat.two_pow_pos _) (by
        change 2 ^ level.val < 2 ^ level.val + index.val + 1
        omega)
      have currentInverse :
          ((current.1.read (rowRead frame.arrays.c (oldRow level index))).toNat :
            ZMod curve.field.modulus) =
            (((current.1.read (rowRead frame.arrays.x (layerSeed window level))).toNat :
              ZMod curve.field.modulus) -
              (current.1.read (rowRead frame.arrays.x (oldRow level index))).toNat)⁻¹ := by
        rw [established.2.2.1, (established.2.1 (layerSeed window level) (Nat.le_refl _)).1,
          (established.2.1 (oldRow level index) (Nat.le_of_lt oldBounds.2)).1]
        exact inverse index
      have actual := frame.extendRecord_coordinateValue curve (layerSeed window level)
        (oldRow level index) (newRow level index) environment current
        ((oldRow level index).val • point) ((layerSeed window level).val • point)
        (established.1.modulus.trans loaded) currentOld currentSeed
        (Ne.symm (layer_coordinate_x_ne curve frame level index current.1 point large
          currentSeed currentOld)) currentInverse
      rw [layer_scalar_sum] at actual
      refine ⟨OriginalInputs.trans frame before.1 current.1 _ established.1
        (frame.extendRecord_originalInputs curve.field _ _ _ environment current), ?_, ?_, ?_⟩
      · intro row below
        have different : row ≠ newRow level index := by
          intro same
          have values := congrArg (fun address : Fin (2 ^ window) => address.val) same
          dsimp only [newRow] at values
          omega
        exact ⟨(frame.extendRecord_read_other_row curve.field _ _ _ environment current
          frame.arrays.x row different).trans (established.2.1 row below).1,
          (frame.extendRecord_read_other_row curve.field _ _ _ environment current
            frame.arrays.y row different).trans (established.2.1 row below).2⟩
      · intro row
        exact (extendRecord_read_inverse frame curve.field _ _ _ environment current row).trans
          (established.2.2.1 row)
      · intro row positive below
        by_cases same : row = newRow level index
        · subst row
          exact actual
        · rw [frame.extendRecord_read_other_row curve.field _ _ _ environment current
            frame.arrays.x row same,
            frame.extendRecord_read_other_row curve.field _ _ _ environment current
              frame.arrays.y row same]
          apply established.2.2.2 row positive
          have different : row.val ≠ 2 ^ level.val + (index.val + 1) :=
            fun equal => same (Fin.ext equal)
          omega) before ⟨OriginalInputs.refl frame before.1, fun _ _ => ⟨rfl, rfl⟩,
            fun _ => rfl, by simpa only [Nat.add_zero] using rows⟩
  have frontier : 2 ^ level.val + layerCount level + 1 = 2 ^ (level.val + 1) := by
    have positive := Nat.two_pow_pos level.val
    rw [pow_succ]
    dsimp only [layerCount]
    omega
  have result := completed.2.2.2
  rw [frontier] at result
  exact result

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
