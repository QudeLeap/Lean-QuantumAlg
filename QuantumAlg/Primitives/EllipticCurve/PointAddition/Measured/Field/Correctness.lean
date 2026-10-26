/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Field
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.Mathematics

/-!
# Complete affine field law, including the reachable exceptional branch

The original active exclusions suffice; no reverse-addition restriction is added.
These proofs depend only on the existing field and group mathematics.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition

noncomputable section

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The original active point exclusions imply the first denominator is nonzero. -/
lemma firstDifference_ne_zero (P Q : AffinePoint E)
    (allowed : affineAllowed true P Q) : firstDifference P.x Q.x ≠ 0 := by
  obtain ⟨different, inverseDifferent⟩ := allowed rfl
  exact sub_ne_zero.mpr (genericAddDomain_of_ne_of_ne_negate E P Q different inverseDifferent)

/-- The actual first quotient is the independent affine secant slope. -/
lemma slope_eq_generic (P Q : AffinePoint E) (domain : GenericAddDomain P Q) :
    slope P.x P.y Q.x Q.y = genericAddSlope E P Q := by
  rw [genericAddSlope_eq_secant_quotient E P Q domain]
  rfl

/-- The second multiplier is zero exactly when the result shares the fixed x coordinate. -/
lemma secondDifference_eq (P Q : AffinePoint E) (domain : GenericAddDomain P Q) :
    secondDifference P.x P.y Q.x Q.y = Q.x - genericAddX E P Q := by
  have known := GenericPointAddition.InPlace.PointSemantics.secondDenominator_true_eq E P Q domain
  rw [GenericPointAddition.InPlace.Semantics.secondDenominator, if_pos rfl,
    GenericPointAddition.InPlace.PointSemantics.selectedSlope_true_eq_genericAddSlope
      E P Q domain] at known
  rw [secondDifference, slope_eq_generic E P Q domain, firstDifference]
  linear_combination known

private lemma result_group (P Q : AffinePoint E) (domain : GenericAddDomain P Q) :
    P.toMathlib + Q.toMathlib = (genericAddPoint E P Q domain).toMathlib :=
  genericAdd_group_law_mathlib E P Q domain

private lemma result_eq_negate (P Q : AffinePoint E) (domain : GenericAddDomain P Q)
    (sameX : (genericAddPoint E P Q domain).x = Q.x) :
    genericAddPoint E P Q domain = AffinePoint.negate Q := by
  rcases (WeierstrassCurve.Affine.Point.X_eq_iff
      (W := E.toWeierstrassCurve.toAffine)
      (h₁ := (genericAddPoint E P Q domain).nonsingular) (h₂ := Q.nonsingular)).mp sameX with
    same | opposite
  · exfalso
    have samePoint : (genericAddPoint E P Q domain).toMathlib = Q.toMathlib := by
      simpa only [AffinePoint.toMathlib] using same
    have zero : P.toMathlib = 0 := by
      apply add_right_cancel (b := Q.toMathlib)
      simpa only [zero_add] using (result_group E P Q domain).trans samePoint
    exact (WeierstrassCurve.Affine.Point.some_ne_zero P.nonsingular) zero
  · have oppositePoint : (genericAddPoint E P Q domain).toMathlib = -Q.toMathlib := by
      simpa only [AffinePoint.toMathlib] using opposite
    have samePoint : (genericAddPoint E P Q domain).toMathlib =
        (AffinePoint.negate Q).toMathlib := by
      rw [AffinePoint.negate_toMathlib]
      exact oppositePoint
    have coordinates := WeierstrassCurve.Affine.Point.some.inj samePoint
    exact AffinePoint.ext_coordinates _ _ coordinates.1 coordinates.2

private lemma negate_self_of_two_mul_y_zero (R : AffinePoint E)
    (zero : (2 : ZMod p) * R.y = 0) : AffinePoint.negate R = R := by
  apply AffinePoint.ext_coordinates
  · rfl
  · have same : -R.y = R.y := by linear_combination -zero
    simpa [toWeierstrassCurve, WeierstrassCurve.Affine.negY] using same

private lemma exceptional_double_domain (P Q : AffinePoint E)
    (domain : GenericAddDomain P Q)
    (sameX : (genericAddPoint E P Q domain).x = Q.x) :
    GenericDoubleDomain (AffinePoint.negate Q) := by
  intro zero
  have same := negate_self_of_two_mul_y_zero E (AffinePoint.negate Q) zero
  have negateSame : AffinePoint.negate Q = Q := by
    calc
      AffinePoint.negate Q = AffinePoint.negate (AffinePoint.negate Q) := same.symm
      _ = Q := AffinePoint.negate_negate Q
  have resultSame : (genericAddPoint E P Q domain).toMathlib = Q.toMathlib :=
    congrArg AffinePoint.toMathlib ((result_eq_negate E P Q domain sameX).trans negateSame)
  have pointZero : P.toMathlib = 0 := by
    apply add_right_cancel (b := Q.toMathlib)
    simpa only [zero_add] using (result_group E P Q domain).trans resultSame
  exact (WeierstrassCurve.Affine.Point.some_ne_zero P.nonsingular) pointZero

private lemma exceptional_coordinates (P Q : AffinePoint E)
    (domain : GenericAddDomain P Q)
    (sameX : (genericAddPoint E P Q domain).x = Q.x) :
    doubleX E (AffinePoint.negate Q) = P.x ∧ doubleY E (AffinePoint.negate Q) = P.y := by
  have doubleDomain := exceptional_double_domain E P Q domain sameX
  have sum : P.toMathlib + Q.toMathlib = -Q.toMathlib := by
    rw [result_group E P Q domain, result_eq_negate E P Q domain sameX,
      AffinePoint.negate_toMathlib]
  have input : P.toMathlib = (AffinePoint.negate Q).toMathlib +
      (AffinePoint.negate Q).toMathlib := by
    calc
      P.toMathlib = (P.toMathlib + Q.toMathlib) + -Q.toMathlib := by abel
      _ = -Q.toMathlib + -Q.toMathlib := by rw [sum]
      _ = _ := by rw [AffinePoint.negate_toMathlib]
  have doubled : WeierstrassCurve.Affine.Point.some
      (doubleX E (AffinePoint.negate Q)) (doubleY E (AffinePoint.negate Q))
      (double_nonsingular E (AffinePoint.negate Q) doubleDomain) = P.toMathlib := by
    rw [← double_group_law_mathlib E (AffinePoint.negate Q) doubleDomain]
    exact input.symm
  have coordinates := WeierstrassCurve.Affine.Point.some.inj doubled
  exact ⟨coordinates.1, coordinates.2⟩

/-- A reachable zero second multiplier makes the slope the same total classical constant. -/
lemma exceptional_slope (P Q : AffinePoint E) (domain : GenericAddDomain P Q)
    (zero : secondDifference P.x P.y Q.x Q.y = 0) :
    slope P.x P.y Q.x Q.y = exceptionalSlope E Q := by
  have sameX : (genericAddPoint E P Q domain).x = Q.x := by
    rw [secondDifference_eq E P Q domain] at zero
    exact (sub_eq_zero.mp zero).symm
  have coordinates := exceptional_coordinates E P Q domain sameX
  rw [exceptionalSlope, coordinates.1, coordinates.2]
  rfl

/-- The normal selector supplies the multiplier domain internally, including coherent control. -/
lemma normalControl_true (control : Bool) (difference : ZMod p)
    (active : normalControl control difference = true) :
    control = true ∧ difference ≠ 0 := by
  simpa [normalControl] using active

/-- Every inactive binary-field input is preserved without a denominator premise. -/
lemma fieldOutput_false (Q : AffinePoint E) (x y : ZMod p) :
    fieldOutput E Q false x y = (x, y) := rfl

/-- Both active branches give the original generic affine point without a reverse-domain premise. -/
lemma fieldOutput_true (P Q : AffinePoint E) (domain : GenericAddDomain P Q) :
    fieldOutput E Q true P.x P.y = (genericAddX E P Q, genericAddY E P Q) := by
  have outputY := GenericPointAddition.InPlace.PointSemantics.selectedOutputY_true E P Q domain
  rw [GenericPointAddition.InPlace.Semantics.selectedOutputY, if_pos rfl,
    GenericPointAddition.InPlace.PointSemantics.selectedSlope_true_eq_genericAddSlope
      E P Q domain,
    GenericPointAddition.InPlace.PointSemantics.secondDenominator_true_eq E P Q domain] at outputY
  have xResult : Q.x - secondDifference P.x P.y Q.x Q.y = genericAddX E P Q := by
    rw [secondDifference_eq E P Q domain]
    ring
  have yResult :
      (if secondDifference P.x P.y Q.x Q.y = 0 then
        slope P.x P.y Q.x Q.y - exceptionalSlope E Q
      else secondDifference P.x P.y Q.x Q.y * slope P.x P.y Q.x Q.y) - Q.y =
      genericAddY E P Q := by
    by_cases zero : secondDifference P.x P.y Q.x Q.y = 0
    · rw [if_pos zero, exceptional_slope E P Q domain zero, sub_self, zero_sub]
      rw [← slope_eq_generic E P Q domain, ← secondDifference_eq E P Q domain, zero,
        mul_zero, zero_sub] at outputY
      exact outputY
    · rw [if_neg zero, secondDifference_eq E P Q domain, slope_eq_generic E P Q domain]
      simpa only [mul_comm] using outputY
  exact Prod.ext xResult yResult

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
