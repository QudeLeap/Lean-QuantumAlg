/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Final.Denominators
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Domain.Exceptional

/-!
# The original paid final C/D batch supplies every real tangent inverse

All positive original addresses retain their original prime point order.
The actual negative-tangent words are therefore nonzero and feed the real
total batch inverse. The returned C word is the inverse required by the
following original fifteen-slot row conversion, on that same actual Store.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width window : Nat}
  (frame : TableFrame ctx width (2 ^ window))

omit [BitWord.Selected model] in
/-- Original positive rows exclude the actual negative-tangent denominator zero. -/
lemma coordinateRowsValue_negativeTangent_ne_zero (curve : CurveSpec width)
    (point : Point curve) (order : Nat) (prime : order.Prime) (large : 3 < order)
    (original : addOrderOf point = order) (tableFits : 2 ^ window < order)
    (store : Store ctx) (rows : frame.CoordinateRowsValue curve point (2 ^ window) store)
    (row : Fin (2 ^ window)) (positive : 0 < row.val) :
    -((2 : ZMod curve.field.modulus) *
      (store.read (rowRead frame.arrays.y row)).toNat) ≠ 0 := by
  have value := rows row positive row.isLt
  have finiteOrder : 3 < addOrderOf (.some
      ((store.read (rowRead frame.arrays.x row)).toNat : ZMod curve.field.modulus)
      ((store.read (rowRead frame.arrays.y row)).toNat : ZMod curve.field.modulus)
      value.finite : Point curve) := by
    rw [value.represents, prime_order_nsmul point order row.val prime original positive
      (lt_trans row.isLt tableFits)]
    exact large
  exact (window_row_denominators_of_order curve _ _ value.finite finiteOrder).1

/-- Every returned actual C row is the inverse of its original negative tangent value. -/
lemma finalInvertedRecord_inverse (curve : CurveSpec width)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (point : Point curve) (order : Nat) (prime : order.Prime) (large : 3 < order)
    (original : addOrderOf point = order) (tableFits : 2 ^ window < order)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (zero : (before.1.read frame.zero).toNat = 0)
    (one : (before.1.read frame.one).toNat = 1)
    (rows : frame.CoordinateRowsValue curve point (2 ^ window) before.1)
    (index : Fin (2 ^ window - 1)) :
    let denominators := (frame.finalDenominatorsRecord curve.field environment before).1
    let returned := (frame.batch.valueRecord curve.field (2 ^ window - 1) finalBatchFits
      environment denominators).1.1
    ((returned.read (rowRead frame.arrays.c (nonzeroRow window index))).toNat :
      ZMod curve.field.modulus) =
      (-((2 : ZMod curve.field.modulus) *
        (before.1.read (rowRead frame.arrays.y (nonzeroRow window index))).toNat))⁻¹ := by
  let denominators := (frame.finalDenominatorsRecord curve.field environment before).1
  let values : Nat → ZMod curve.field.modulus := fun position =>
    if within : position < 2 ^ window - 1 then
      -((2 : ZMod curve.field.modulus) *
        (before.1.read (rowRead frame.arrays.y (nonzeroRow window ⟨position, within⟩))).toNat)
    else 0
  have retained := frame.finalDenominatorsRecord_originalInputs curve.field environment before
  have nonzero : ∀ position < 2 ^ window - 1, values position ≠ 0 := by
    intro position within
    dsimp only [values]
    rw [dif_pos within]
    exact frame.coordinateRowsValue_negativeTangent_ne_zero curve point order prime large
      original tableFits before.1 rows (nonzeroRow window ⟨position, within⟩) (by
        change 0 < position + 1
        omega)
  have represented : ∀ row : Fin (2 ^ window), 1 ≤ row.val →
      row.val ≤ 2 ^ window - 1 →
      ((denominators.1.read (rowRead frame.arrays.c row)).toNat :
        ZMod curve.field.modulus) = values (row.val - 1) := by
    intro row positive within
    have bounded : row.val - 1 < 2 ^ window - 1 := by omega
    let selected : Fin (2 ^ window - 1) := ⟨row.val - 1, bounded⟩
    have same : nonzeroRow window selected = row := Fin.ext (by
      dsimp only [nonzeroRow, selected]
      omega)
    change (((frame.finalDenominatorsRecord curve.field environment before).1.1.read
      (rowRead frame.arrays.c row)).toNat : ZMod curve.field.modulus) = _
    rw [← same,
      frame.finalDenominatorsRecord_read_result curve.field environment before loaded zero]
    simp only [values, nonzeroRow, selected, Nat.add_sub_cancel, dif_pos bounded]
  have actual := frame.batchRecord_denominator_inverse curve.field environment (2 ^ window - 1)
    finalBatchFits values denominators (retained.modulus.trans loaded)
    (by rw [retained.inputs frame.one (by simp)]; exact one) nonzero represented
    (nonzeroRow window index) (by change 1 ≤ index.val + 1; omega) (by
      change index.val + 1 ≤ 2 ^ window - 1
      have bounded := index.isLt
      omega)
  have cast := congrArg (fun value : Nat => (value : ZMod curve.field.modulus)) actual
  rw [ZMod.natCast_zmod_val] at cast
  simpa only [values, nonzeroRow, Nat.add_sub_cancel, dif_pos index.isLt] using cast

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
