/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Tables.Digit
import Mathlib.GroupTheory.OrderOfElement

/-!
# Finite original group rows selected by the actual whole digit

The genuine ordinary selector excludes identity row zero. The same full
row bound and original base-point order then exclude the group identity
for its scalar multiple. Its coordinates are obtained from that actual
point, without a fictitious finite identity or an additional domain promise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Tables

noncomputable section

open ClassicalAlgorithms.EllipticCurve

/-- An enabled full original row below the original order is a nonidentity scalar point. -/
lemma selectedPoint_ne_zero (curve : CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (state : Raw) (order : Nat)
    (original : addOrderOf point = order) (tableFits : 2 ^ (width + 1) < order)
    (active : QueryInsertion.querySelected stream width bounded false state = true) :
    (selectedRow stream width bounded state).val • point ≠ 0 := by
  have nonzero : (selectedRow stream width bounded state).val ≠ 0 :=
    (querySelected_ordinary_iff stream width bounded state).mp active
  apply nsmul_ne_zero_of_lt_addOrderOf nonzero
  rw [original]
  exact (selectedRow stream width bounded state).isLt.trans tableFits

/-- The same enabled scalar point supplies its own actual nonsingular finite coordinates. -/
lemma selectedPoint_finite (curve : CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (state : Raw) (order : Nat)
    (original : addOrderOf point = order) (tableFits : 2 ^ (width + 1) < order)
    (active : QueryInsertion.querySelected stream width bounded false state = true) :
    ∃ x y : ZMod curve.field.modulus,
      ∃ finite : curve.curve.toWeierstrassCurve.toAffine.Nonsingular x y,
        (selectedRow stream width bounded state).val • point =
          (.some x y finite : ClassicalAlgorithms.EllipticCurve.Point curve) := by
  have nonzero := selectedPoint_ne_zero curve point stream width bounded state order
    original tableFits active
  generalize (selectedRow stream width bounded state).val • point = selected at nonzero ⊢
  cases selected with
  | zero => exact False.elim (nonzero rfl)
  | some x y finite => exact ⟨x, y, finite, rfl⟩

end

end Tables

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
