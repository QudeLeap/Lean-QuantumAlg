/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Domain

/-!
# Exceptional-slope denominator from the original point order

The finite point obtained by doubling -Q equals -2Q in the original group.
If 2Q and 3Q are nonzero, that point is neither Q nor -Q. The existing
finite-coordinate theorem therefore excludes exactly the exceptional
secant denominator. All witnesses stay in the lower pure curve interface.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open ClassicalAlgorithms.EllipticCurve

noncomputable section

/-- Original nonzero 2Q/3Q domains exclude the actual exceptional secant denominator. -/
lemma exceptional_denominator_ne_zero {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus)
    (finite : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x y)
    (doubled : (.some x y finite : Point spec) + .some x y finite ≠ 0)
    (tripled : ((.some x y finite : Point spec) + .some x y finite) +
      .some x y finite ≠ 0) :
    ShortWeierstrass.doubleX spec x (-y) - x ≠ 0 := by
  let point : Point spec := .some x y finite
  have nonzeroY := finite_y_ne_zero_of_double_ne_zero spec x y finite doubled
  let negativeFinite := ShortWeierstrass.neg_nonsingular spec x y finite
  have negativePoint : (.some x (-y) negativeFinite : Point spec) = -point :=
    (ShortWeierstrass.neg_eval_some spec x y finite).symm
  let doubledFinite := ShortWeierstrass.double_nonsingular spec x (-y) negativeFinite
    (neg_ne_zero.mpr nonzeroY)
  let doubledPoint : Point spec := .some (ShortWeierstrass.doubleX spec x (-y))
    (ShortWeierstrass.doubleY spec x (-y)) doubledFinite
  have doubleGroup : doubledPoint = -point + -point := by
    have actual := ShortWeierstrass.doublePoint_eq_mathlib_double spec x (-y) negativeFinite
      (neg_ne_zero.mpr nonzeroY)
    change doubledPoint = (.some x (-y) negativeFinite : Point spec) +
      .some x (-y) negativeFinite at actual
    exact actual.trans (congrArg (fun value : Point spec => value + value) negativePoint)
  have notPoint : doubledPoint ≠ point := by
    intro same
    have equal : -point + -point = point := doubleGroup.symm.trans same
    apply tripled
    change (point + point) + point = 0
    calc
      (point + point) + point = (point + point) + (-point + -point) :=
        congrArg (fun value => (point + point) + value) equal.symm
      _ = 0 := by abel
  have notNegative : doubledPoint ≠ -point := by
    intro same
    have equal : -point + -point = -point := doubleGroup.symm.trans same
    have zero : -point = 0 := by
      apply add_right_cancel (b := -point)
      simpa only [zero_add] using equal
    exact WeierstrassCurve.Affine.Point.some_ne_zero finite (neg_eq_zero.mp zero)
  exact sub_ne_zero.mpr (ShortWeierstrass.genericFinite_x_ne spec
    (ShortWeierstrass.doubleX spec x (-y)) x
    (ShortWeierstrass.doubleY spec x (-y)) y doubledFinite finite notPoint notNegative)

/-- Original order greater than three supplies both nonzero denominator domains. -/
lemma window_row_denominators_of_order {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus)
    (finite : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x y)
    (large : 3 < addOrderOf (.some x y finite : Point spec)) :
    -((2 : ZMod spec.field.modulus) * y) ≠ 0 ∧
      ShortWeierstrass.doubleX spec x (-y) - x ≠ 0 := by
  have doubled : (.some x y finite : Point spec) + .some x y finite ≠ 0 := by
    have actual : (2 : Nat) • (.some x y finite : Point spec) ≠ 0 :=
      nsmul_ne_zero_of_lt_addOrderOf (by decide) (by omega)
    simpa only [two_nsmul] using actual
  have tripled : ((.some x y finite : Point spec) + .some x y finite) +
      .some x y finite ≠ 0 := by
    have actual : (3 : Nat) • (.some x y finite : Point spec) ≠ 0 :=
      nsmul_ne_zero_of_lt_addOrderOf (by decide) large
    simpa only [show (3 : Nat) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul] using actual
  exact ⟨negative_tangent_denominator_ne_zero spec x y finite doubled,
    exceptional_denominator_ne_zero spec x y finite doubled tripled⟩

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
