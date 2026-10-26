/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Classical.EllipticCurve.Formulas
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel

/-!
# Original nonzero domains of the five-table construction

Finite scalar rows below the original base-point order are distinct and
not inverses when their index sum is below that same order. Therefore the
literal binary-layer secant denominators are nonzero. The nonvertical
tangent domain and negative exceptional-slope formula use only the existing
pure fixed-width curve interface, with no reverse dependency on Primitives.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open ClassicalAlgorithms.EllipticCurve

noncomputable section

/-- Every positive scalar below a prime original order retains that exact original order. -/
lemma prime_order_nsmul {G : Type*} [AddGroup G] (base : G) (order index : Nat)
    (prime : order.Prime) (original : addOrderOf base = order)
    (positive : 0 < index) (bounded : index < order) :
    addOrderOf (index • base) = order := by
  have coprime : order.Coprime index := prime.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt positive bounded)
  rw [← original] at coprime
  exact coprime.addOrderOf_nsmul.trans original

/-- Original finite rows with separated scalar indices have different actual affine x values. -/
lemma scalar_finite_x_ne {width : Nat} (spec : CurveSpec width) (base : Point spec)
    (first second : Nat) (positive : 0 < second) (ordered : second < first)
    (bounded : first + second < addOrderOf base)
    (firstX firstY secondX secondY : ZMod spec.field.modulus)
    (firstFinite : spec.curve.toWeierstrassCurve.toAffine.Nonsingular firstX firstY)
    (secondFinite : spec.curve.toWeierstrassCurve.toAffine.Nonsingular secondX secondY)
    (firstValue : (.some firstX firstY firstFinite : Point spec) = first • base)
    (secondValue : (.some secondX secondY secondFinite : Point spec) = second • base) :
    firstX ≠ secondX := by
  apply ShortWeierstrass.genericFinite_x_ne spec firstX secondX firstY secondY
    firstFinite secondFinite
  · intro equal
    have injective : (Set.Iio (addOrderOf base)).InjOn (fun index : Nat => index • base) :=
      nsmul_injOn_Iio_addOrderOf
    have scalarEqual := injective (by change first < _; omega)
      (by change second < _; omega) (firstValue.symm.trans (equal.trans secondValue))
    omega
  · intro inverse
    have scalarInverse : first • base = -(second • base) := by
      rw [← firstValue, ← secondValue]
      exact inverse
    have nonzero : (first + second) • base ≠ 0 :=
      nsmul_ne_zero_of_lt_addOrderOf (by omega) bounded
    apply nonzero
    rw [add_nsmul, scalarInverse, neg_add_cancel]

/-- Nonzero doubling of a finite point excludes the zero-y tangent branch. -/
lemma finite_y_ne_zero_of_double_ne_zero {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus)
    (finite : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x y)
    (doubled : (.some x y finite : Point spec) + .some x y finite ≠ 0) : y ≠ 0 := by
  intro zero
  subst y
  apply doubled
  exact ShortWeierstrass.double_eval_eq_infinity_of_y_eq_zero spec x finite

/-- The literal final batch denominator -2y is nonzero on the original doubling domain. -/
lemma negative_tangent_denominator_ne_zero {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus)
    (finite : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x y)
    (doubled : (.some x y finite : Point spec) + .some x y finite ≠ 0) :
    -((2 : ZMod spec.field.modulus) * y) ≠ 0 :=
  neg_ne_zero.mpr (mul_ne_zero (ShortWeierstrass.two_ne_zero spec)
    (finite_y_ne_zero_of_double_ne_zero spec x y finite doubled))

/-- The original exceptional secant slope, expressed through the lower pure curve formulas. -/
def exceptionalSlope {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus) : ZMod spec.field.modulus :=
  (ShortWeierstrass.doubleY spec x (-y) - y) /
    (ShortWeierstrass.doubleX spec x (-y) - x)

/-- The final actual table's tangent at -Q is exactly the negative original exceptional slope. -/
lemma negative_exceptionalSlope_eq_tangent {width : Nat} (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus)
    (denominator : ShortWeierstrass.doubleX spec x (-y) - x ≠ 0) :
    -exceptionalSlope spec x y = ShortWeierstrass.doubleSlope spec x (-y) := by
  have numerator : ShortWeierstrass.doubleY spec x (-y) - y =
      -ShortWeierstrass.doubleSlope spec x (-y) *
        (ShortWeierstrass.doubleX spec x (-y) - x) := by
    unfold ShortWeierstrass.doubleY
    ring
  rw [exceptionalSlope, numerator, mul_div_cancel_right₀ _ denominator, neg_neg]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
