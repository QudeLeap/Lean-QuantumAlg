/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Mathematics

/-!
# Independent field and point mathematics of controlled affine addition

The selected field coordinates follow the controlled affine point update
and disabled control branch of Algorithm 1 [RNSL17, ECDLP.tex:488-498,514-550].
The proofs below establish the two nonzero denominators from explicit forward
and reverse affine domains. These definitions and proofs refer to no
arithmetic backend, register layout, gate list, resource witness or execution
result.

The measured arithmetic implementation can therefore reuse the exact
mathematical target and explicit exception boundary independently of its
choice of field representation or workspace.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.GenericPointAddition.InPlace

noncomputable section

namespace Semantics

/-- Numerator after Algorithm 1's controlled subtraction of `y2` from `y1`:
`y1 - y2` when enabled and `y1` otherwise [RNSL17, ECDLP.tex:515,535]. -/
def selectedNumerator {p : Nat} (control : Bool)
    (y1 y2 : ZMod p) : ZMod p :=
  if control then y1 - y2 else y1

/-- Field slope computed in both control branches by Algorithm 1's first
inversion and multiplication [RNSL17, ECDLP.tex:516-517,536-537]. -/
def selectedSlope {p : Nat} (control : Bool)
    (x1 y1 x2 y2 : ZMod p) : ZMod p :=
  selectedNumerator control y1 y2 * (x1 - x2)⁻¹

/-- Input to Algorithm 1's second inversion pair, after the controlled
squared-slope subtraction and `3 * x2` addition and before the controlled
x-negation [RNSL17, ECDLP.tex:520-528,540-548]. -/
def secondDenominator {p : Nat} (control : Bool)
    (x1 y1 x2 y2 : ZMod p) : ZMod p :=
  if control then
    (x1 - x2) - selectedSlope control x1 y1 x2 y2 ^ 2 + 3 * x2
  else x1 - x2

/-- Field x-coordinate after Algorithm 1's controlled negation and final
addition of `x2` [RNSL17, ECDLP.tex:528-530,548-550]. -/
def selectedOutputX {p : Nat} (control : Bool)
    (x1 y1 x2 y2 : ZMod p) : ZMod p :=
  (if control then -secondDenominator control x1 y1 x2 y2
    else secondDenominator control x1 y1 x2 y2) + x2

/-- Field y-coordinate after Algorithm 1's slope multiplication and final
controlled subtraction of `y2` [RNSL17, ECDLP.tex:524,529,544,549]. -/
def selectedOutputY {p : Nat} (control : Bool)
    (x1 y1 x2 y2 : ZMod p) : ZMod p :=
  if control then
    selectedSlope control x1 y1 x2 y2 *
        secondDenominator control x1 y1 x2 y2 - y2
  else
    selectedSlope control x1 y1 x2 y2 *
      secondDenominator control x1 y1 x2 y2

end Semantics

namespace PointSemantics

/-- Point selected by the controlled update specified in Algorithm 1's
caption [RNSL17, ECDLP.tex:510]. -/
def selectedPoint {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (control : Bool) (P Q : AffinePoint E)
    (hforward : GenericAddDomain P Q) : AffinePoint E :=
  if control then genericAddPoint E P Q hforward else P

theorem selectedSlope_true_eq_genericAddSlope
    {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P Q : AffinePoint E) (hforward : GenericAddDomain P Q) :
    Semantics.selectedSlope true P.x P.y Q.x Q.y =
      genericAddSlope E P Q := by
  rw [genericAddSlope_eq_secant_quotient E P Q hforward]
  simp [Semantics.selectedSlope, Semantics.selectedNumerator,
    genericAddNumerator, genericAddDenominator, div_eq_mul_inv]

theorem secondDenominator_true_eq
    {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P Q : AffinePoint E) (hforward : GenericAddDomain P Q) :
    Semantics.secondDenominator true P.x P.y Q.x Q.y =
      Q.x - genericAddX E P Q := by
  rw [Semantics.secondDenominator, if_pos rfl]
  rw [selectedSlope_true_eq_genericAddSlope E P Q hforward]
  simp [genericAddX,
    genericAddXFromSlope, toWeierstrassCurve,
    WeierstrassCurve.Affine.addX]
  ring

private theorem slope_mul_denominator
    {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P Q : AffinePoint E) (hforward : GenericAddDomain P Q) :
    genericAddSlope E P Q * (P.x - Q.x) = P.y - Q.y := by
  rw [genericAddSlope_eq_secant_quotient E P Q hforward]
  simp only [genericAddNumerator, genericAddDenominator, div_eq_mul_inv]
  have hdenominator : P.x - Q.x ≠ 0 := sub_ne_zero.mpr hforward
  calc
    (P.y - Q.y) * (P.x - Q.x)⁻¹ * (P.x - Q.x) =
        (P.y - Q.y) * ((P.x - Q.x)⁻¹ * (P.x - Q.x)) := by ring
    _ = P.y - Q.y := by rw [inv_mul_cancel₀ hdenominator, mul_one]

theorem selectedOutputX_false
    {p : Nat} [Fact p.Prime] (P Q : ZMod p)
    (y1 y2 : ZMod p) :
    Semantics.selectedOutputX false P y1 Q y2 = P := by
  simp [Semantics.selectedOutputX, Semantics.secondDenominator]

theorem selectedOutputY_false
    {p : Nat} [Fact p.Prime] (x1 y1 x2 y2 : ZMod p)
    (hforward : x1 ≠ x2) :
    Semantics.selectedOutputY false x1 y1 x2 y2 = y1 := by
  have hdenominator : x1 - x2 ≠ 0 := sub_ne_zero.mpr hforward
  simp [Semantics.selectedOutputY, Semantics.selectedSlope,
    Semantics.selectedNumerator, Semantics.secondDenominator, hdenominator]

theorem selectedOutputX_true
    {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P Q : AffinePoint E) (hforward : GenericAddDomain P Q) :
    Semantics.selectedOutputX true P.x P.y Q.x Q.y =
      genericAddX E P Q := by
  rw [Semantics.selectedOutputX, if_pos rfl,
    secondDenominator_true_eq E P Q hforward]
  ring

theorem selectedOutputY_true
    {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P Q : AffinePoint E) (hforward : GenericAddDomain P Q) :
    Semantics.selectedOutputY true P.x P.y Q.x Q.y =
      genericAddY E P Q := by
  rw [Semantics.selectedOutputY, if_pos rfl,
    selectedSlope_true_eq_genericAddSlope E P Q hforward,
    secondDenominator_true_eq E P Q hforward]
  have line := slope_mul_denominator E P Q hforward
  calc
    genericAddSlope E P Q * (Q.x - genericAddX E P Q) - Q.y =
        genericAddSlope E P Q * (P.x - genericAddX E P Q) - P.y := by
      linear_combination -line
    _ = genericAddY E P Q := by
      rw [genericAddY, genericAddYFromSlope,
        WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.negAddY]
      simp only [toWeierstrassCurve, zero_mul, sub_zero]
      change
        genericAddSlope E P Q * (P.x - genericAddX E P Q) - P.y =
          -(genericAddSlope E P Q * (genericAddX E P Q - P.x) + P.y)
      ring

theorem selectedOutputs_eq_point
    {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (control : Bool) (P Q : AffinePoint E)
    (hforward : GenericAddDomain P Q) :
    Semantics.selectedOutputX control P.x P.y Q.x Q.y =
        (selectedPoint E control P Q hforward).x ∧
      Semantics.selectedOutputY control P.x P.y Q.x Q.y =
        (selectedPoint E control P Q hforward).y := by
  cases control with
  | false =>
      exact
        ⟨selectedOutputX_false P.x Q.x P.y Q.y,
          selectedOutputY_false P.x P.y Q.x Q.y hforward⟩
  | true =>
      exact
        ⟨selectedOutputX_true E P Q hforward,
          selectedOutputY_true E P Q hforward⟩

theorem secondDenominator_ne_zero_of_domains
    {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (control : Bool) (P Q : AffinePoint E)
    (hforward : GenericAddDomain P Q)
    (hreverse : control = true →
      GenericAddDomain (genericAddPoint E P Q hforward) Q) :
    Semantics.secondDenominator control P.x P.y Q.x Q.y ≠ 0 := by
  cases control with
  | false =>
      simpa [Semantics.secondDenominator] using
        (sub_ne_zero.mpr hforward)
  | true =>
      rw [secondDenominator_true_eq E P Q hforward]
      exact sub_ne_zero.mpr (Ne.symm (hreverse rfl))

/-- Affine negation is inversion in the multiplicative group-point wrapper. -/
theorem negate_toGroupPoint
    {p : Nat} {E : PrimeFieldShortWeierstrass p} (Q : AffinePoint E) :
    (AffinePoint.negate Q).toGroupPoint = Q.toGroupPoint⁻¹ := by
  exact congrArg
    (fun value : E.MathlibPoint => (⟨value⟩ : GroupPoint E))
    (AffinePoint.negate_toMathlib Q)

/-- Every finite affine point is nonidentity in the total group carrier. -/
theorem toGroupPoint_ne_one
    {p : Nat} {E : PrimeFieldShortWeierstrass p} (P : AffinePoint E) :
    P.toGroupPoint ≠ 1 := by
  intro equality
  have underlying := congrArg GroupPoint.toMathlib equality
  change P.toMathlib = 0 at underlying
  exact WeierstrassCurve.Affine.Point.some_ne_zero P.nonsingular underlying

/-- Group-level exclusion of `Q` and `-Q` implies the first affine domain,
matching the generic-case condition [RNSL17, ECDLP.tex:488]. -/
theorem forwardDomain_of_group_conditions
    {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P Q : AffinePoint E)
    (hsame : P.toGroupPoint ≠ Q.toGroupPoint)
    (hinverse : P.toGroupPoint ≠ Q.toGroupPoint⁻¹) :
    GenericAddDomain P Q := by
  apply genericAddDomain_of_ne_of_ne_negate E P Q
  · intro equality
    exact hsame (congrArg AffinePoint.toGroupPoint equality)
  · intro equality
    apply hinverse
    rw [← negate_toGroupPoint Q]
    exact congrArg AffinePoint.toGroupPoint equality

/-- The generic affine output represents multiplication by the addend in the
group-point wrapper. -/
theorem genericAddPoint_toGroupPoint
    {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P Q : AffinePoint E) (hforward : GenericAddDomain P Q) :
    (genericAddPoint E P Q hforward).toGroupPoint =
      P.toGroupPoint * Q.toGroupPoint := by
  exact congrArg
    (fun value : E.MathlibPoint => (⟨value⟩ : GroupPoint E))
    (by
      simpa [groupPointEquiv, AffinePoint.toGroupPoint, genericAddPoint,
        AffinePoint.toMathlib] using
        (genericAdd_group_law_mathlib E P Q hforward).symm)

/-- The strict active exclusion `P ≠ -2Q` supplies the second affine domain
used to clean the recomputed slope [RNSL17, ECDLP.tex:490-492,525-527].
This theorem derives that exclusion's sufficiency for the second denominator;
Algorithm 1's caption does not state this additional exclusion
[RNSL17, ECDLP.tex:510]. -/
theorem reverseDomain_of_double_inverse_exclusion
    {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P Q : AffinePoint E) (hforward : GenericAddDomain P Q)
    (hdouble : P.toGroupPoint ≠
      (Q.toGroupPoint * Q.toGroupPoint)⁻¹) :
    GenericAddDomain (genericAddPoint E P Q hforward) Q := by
  let result := genericAddPoint E P Q hforward
  have resultLaw : result.toGroupPoint =
      P.toGroupPoint * Q.toGroupPoint :=
    genericAddPoint_toGroupPoint E P Q hforward
  have resultNeQ : result ≠ Q := by
    intro equality
    have groupEquality := congrArg AffinePoint.toGroupPoint equality
    rw [resultLaw] at groupEquality
    have pointIdentity : P.toGroupPoint = 1 := by
      calc
        P.toGroupPoint =
            (P.toGroupPoint * Q.toGroupPoint) * Q.toGroupPoint⁻¹ := by simp
        _ = Q.toGroupPoint * Q.toGroupPoint⁻¹ := by rw [groupEquality]
        _ = 1 := by simp
    exact toGroupPoint_ne_one P pointIdentity
  have resultNeInverse : result ≠ AffinePoint.negate Q := by
    intro equality
    have groupEquality := congrArg AffinePoint.toGroupPoint equality
    rw [resultLaw, negate_toGroupPoint Q] at groupEquality
    apply hdouble
    calc
      P.toGroupPoint =
          (P.toGroupPoint * Q.toGroupPoint) * Q.toGroupPoint⁻¹ := by simp
      _ = Q.toGroupPoint⁻¹ * Q.toGroupPoint⁻¹ := by rw [groupEquality]
      _ = (Q.toGroupPoint * Q.toGroupPoint)⁻¹ := by simp
  exact genericAddDomain_of_ne_of_ne_negate E result Q resultNeQ
    resultNeInverse

end PointSemantics

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.GenericPointAddition.InPlace
