/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Generic.Pipeline

/-!
# Exceptional affine cleanup mathematics

This leaf isolates the finite exceptional branch in which the forward generic
sum shares its `x` coordinate with the fixed addend.  The generic reverse-add
route is then unavailable; the original point is recovered by doubling the
finite inverse of the fixed addend.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace Pipeline
namespace ExceptionalCleanupMath

noncomputable section

variable [params : Arithmetic.VariableModularMul.Parameters]

variable {E : PrimeFieldShortWeierstrass params.modulus.val}
  [Fact params.modulus.val.Prime]
  {Q : AffinePoint E}

private theorem negate_eq_self_of_two_mul_y_eq_zero
    (R : AffinePoint E)
    (hzero : (2 : ZMod params.modulus.val) * R.y = 0) :
    AffinePoint.negate R = R := by
  apply AffinePoint.ext_coordinates
  · rfl
  · have hy : -R.y = R.y := by
      linear_combination -hzero
    simpa [toWeierstrassCurve, WeierstrassCurve.Affine.negY] using hy

/-- If the forward generic result shares the fixed addend's `x` coordinate,
the finite input cannot be the identity branch, so the result is the affine
inverse of the addend. -/
theorem resultPoint_eq_negate_of_x_eq
    (P : GenericPointAddition.Input E Q)
    (hx : (resultPoint P).x = Q.x) :
    resultPoint P = AffinePoint.negate Q := by
  rcases (WeierstrassCurve.Affine.Point.X_eq_iff
      (W := E.toWeierstrassCurve.toAffine)
      (h₁ := (resultPoint P).nonsingular) (h₂ := Q.nonsingular)).mp hx with
    hsame | hneg
  · exfalso
    have hsameMathlib : (resultPoint P).toMathlib = Q.toMathlib := by
      simpa only [AffinePoint.toMathlib] using hsame
    have hPzero : P.1.toMathlib = 0 := by
      apply add_right_cancel (b := Q.toMathlib)
      simpa only [zero_add] using
        (resultPoint_group_law_mathlib P).trans hsameMathlib
    exact (WeierstrassCurve.Affine.Point.some_ne_zero P.1.nonsingular) hPzero
  · have hnegMathlib : (resultPoint P).toMathlib = -Q.toMathlib := by
      simpa only [AffinePoint.toMathlib] using hneg
    have hmathlib : (resultPoint P).toMathlib =
        (AffinePoint.negate Q).toMathlib := by
      rw [AffinePoint.negate_toMathlib]
      exact hnegMathlib
    have hcoordinates := WeierstrassCurve.Affine.Point.some.inj hmathlib
    exact AffinePoint.ext_coordinates _ _ hcoordinates.1 hcoordinates.2

/-- The same exceptional `x`-coordinate condition forces the inverse addend
into the nonvertical doubling domain. -/
theorem negate_doubleDomain_of_resultPoint_x_eq
    (P : GenericPointAddition.Input E Q)
    (hx : (resultPoint P).x = Q.x) :
    GenericDoubleDomain (AffinePoint.negate Q) := by
  unfold GenericDoubleDomain
  intro hzero
  have hself : AffinePoint.negate (AffinePoint.negate Q) =
      AffinePoint.negate Q :=
    negate_eq_self_of_two_mul_y_eq_zero (AffinePoint.negate Q) hzero
  have hnegQeq : AffinePoint.negate Q = Q := by
    calc
      AffinePoint.negate Q = AffinePoint.negate (AffinePoint.negate Q) :=
        hself.symm
      _ = Q := AffinePoint.negate_negate Q
  have hresultMathlib : (resultPoint P).toMathlib = Q.toMathlib := by
    exact congrArg AffinePoint.toMathlib
      ((resultPoint_eq_negate_of_x_eq P hx).trans hnegQeq)
  have hPzero : P.1.toMathlib = 0 := by
    apply add_right_cancel (b := Q.toMathlib)
    simpa only [zero_add] using
      (resultPoint_group_law_mathlib P).trans hresultMathlib
  exact (WeierstrassCurve.Affine.Point.some_ne_zero P.1.nonsingular) hPzero

/-- In the exceptional branch, doubling the finite inverse addend recovers
the two affine coordinates of the original generic input. -/
theorem doubleNegate_coordinates_eq_input_of_resultPoint_x_eq
    (P : GenericPointAddition.Input E Q)
    (hx : (resultPoint P).x = Q.x) :
    doubleX E (AffinePoint.negate Q) = P.1.x ∧
      doubleY E (AffinePoint.negate Q) = P.1.y := by
  have hdouble : GenericDoubleDomain (AffinePoint.negate Q) :=
    negate_doubleDomain_of_resultPoint_x_eq P hx
  have hresultMathlib : (resultPoint P).toMathlib =
      (AffinePoint.negate Q).toMathlib :=
    congrArg AffinePoint.toMathlib (resultPoint_eq_negate_of_x_eq P hx)
  have hsum : P.1.toMathlib + Q.toMathlib = -Q.toMathlib := by
    calc
      P.1.toMathlib + Q.toMathlib = (resultPoint P).toMathlib :=
        resultPoint_group_law_mathlib P
      _ = (AffinePoint.negate Q).toMathlib := hresultMathlib
      _ = -Q.toMathlib := AffinePoint.negate_toMathlib Q
  have hinput : P.1.toMathlib =
      (AffinePoint.negate Q).toMathlib +
        (AffinePoint.negate Q).toMathlib := by
    calc
      P.1.toMathlib =
          (P.1.toMathlib + Q.toMathlib) + -Q.toMathlib := by
        abel
      _ = -Q.toMathlib + -Q.toMathlib := by rw [hsum]
      _ = (AffinePoint.negate Q).toMathlib +
          (AffinePoint.negate Q).toMathlib := by
        rw [AffinePoint.negate_toMathlib]
  have hdoubleMathlib :
      WeierstrassCurve.Affine.Point.some
          (doubleX E (AffinePoint.negate Q))
          (doubleY E (AffinePoint.negate Q))
          (double_nonsingular E (AffinePoint.negate Q) hdouble) =
        P.1.toMathlib := by
    rw [← double_group_law_mathlib E (AffinePoint.negate Q) hdouble]
    exact hinput.symm
  have hcoordinates := WeierstrassCurve.Affine.Point.some.inj hdoubleMathlib
  exact ⟨hcoordinates.1, hcoordinates.2⟩

end

end ExceptionalCleanupMath
end Pipeline
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
