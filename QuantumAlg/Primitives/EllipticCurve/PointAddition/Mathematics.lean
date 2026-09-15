/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


module

public import QuantumAlg.Util.EllipticCurve
import all QuantumAlg.Util.EllipticCurve
import Mathlib.Algebra.Field.ZMod

/-!
# Independent affine point-addition mathematics

The original field formulas, source domains, finite point conventions and
Mathlib group laws require no arithmetic execution backend. The generic
addition and doubling routes preserve their original exceptional-point
conditions [PZ03, ecc.tex:525-640; RNSL17, ECDLP.tex:488-580].
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass

variable {p : ℕ}

/-- Reusable generic-domain predicate for affine point addition.  It exposes the
nonexceptional `x₁ ≠ x₂` side condition used by the current finite-affine
generic circuit route [RNSL17, ECDLP.tex:488-580]. -/
def GenericAddDomain {E : PrimeFieldShortWeierstrass p}
    (P Q : AffinePoint E) : Prop :=
  P.x ≠ Q.x

/-- Reusable generic-domain predicate for affine point doubling.  It exposes the
nonvertical-tangent denominator `2y ≠ 0` used by the short-Weierstrass tangent
formula. -/
def GenericDoubleDomain {E : PrimeFieldShortWeierstrass p}
    (P : AffinePoint E) : Prop :=
  (2 : ZMod p) * P.y ≠ 0

/-- Controlled generic addition uses the same generic-domain predicate as
uncontrolled affine addition; the control bit only selects whether the update is
applied. -/
def ControlledAddDomain {E : PrimeFieldShortWeierstrass p}
    (P Q : AffinePoint E) : Prop :=
  GenericAddDomain P Q

/-- The affine-addition denominator used by the generic slope formula. -/
def genericAddDenominator {E : PrimeFieldShortWeierstrass p}
    (P Q : AffinePoint E) : ZMod p :=
  P.x - Q.x

/-- The affine-addition numerator used by the generic slope formula. -/
def genericAddNumerator {E : PrimeFieldShortWeierstrass p}
    (P Q : AffinePoint E) : ZMod p :=
  P.y - Q.y

/-- Generic affine-addition assumptions make the slope denominator nonzero. -/
theorem genericAddDenominator_ne_zero {E : PrimeFieldShortWeierstrass p}
    {P Q : AffinePoint E} (h : GenericAddDomain P Q) :
    genericAddDenominator P Q ≠ 0 := by
  intro hzero
  exact h (sub_eq_zero.mp hzero)

/-- Unit denominator for feeding generic affine addition into the unit-domain
modular-division primitive. -/
def genericAddDenominatorUnit {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (P Q : AffinePoint E) (h : GenericAddDomain P Q) :
    (ZMod p)ˣ :=
  Units.mk0 (genericAddDenominator P Q) (genericAddDenominator_ne_zero h)

@[simp] theorem genericAddDenominatorUnit_val {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (P Q : AffinePoint E) (h : GenericAddDomain P Q) :
    ((genericAddDenominatorUnit P Q h : (ZMod p)ˣ) : ZMod p) =
      genericAddDenominator P Q :=
  rfl


/-- The affine-doubling denominator used by the tangent slope formula. -/
def doubleDenominator {E : PrimeFieldShortWeierstrass p}
    (P : AffinePoint E) : ZMod p :=
  (2 : ZMod p) * P.y

/-- Generic affine-doubling assumptions make the tangent denominator nonzero. -/
theorem doubleDenominator_ne_zero {E : PrimeFieldShortWeierstrass p}
    {P : AffinePoint E} (h : GenericDoubleDomain P) :
    doubleDenominator P ≠ 0 :=
  h

/-- Unit denominator for feeding nonexceptional affine doubling into the
unit-domain modular-division primitive. -/
def doubleDenominatorUnit {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (P : AffinePoint E) (h : GenericDoubleDomain P) :
    (ZMod p)ˣ :=
  Units.mk0 (doubleDenominator P) (doubleDenominator_ne_zero h)

@[simp] theorem doubleDenominatorUnit_val {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (P : AffinePoint E) (h : GenericDoubleDomain P) :
    ((doubleDenominatorUnit P h : (ZMod p)ˣ) : ZMod p) =
      doubleDenominator P :=
  rfl


/-- Generic affine-addition slope for points with distinct `x` coordinates. -/
def genericAddSlope (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P Q : AffinePoint E) : ZMod p :=
  E.toWeierstrassCurve.toAffine.slope P.x Q.x P.y Q.y

/-- Generic affine-addition `x` coordinate computed from an already materialized
slope scratch value. -/
def genericAddXFromSlope (E : PrimeFieldShortWeierstrass p)
    (P Q : AffinePoint E) (slope : ZMod p) : ZMod p :=
  E.toWeierstrassCurve.toAffine.addX P.x Q.x slope

/-- Generic affine-addition `y` coordinate computed from an already materialized
slope scratch value. -/
def genericAddYFromSlope (E : PrimeFieldShortWeierstrass p)
    (P Q : AffinePoint E) (slope : ZMod p) : ZMod p :=
  E.toWeierstrassCurve.toAffine.addY P.x Q.x P.y slope

/-- Generic affine-addition `x` coordinate in short-Weierstrass form. -/
def genericAddX (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P Q : AffinePoint E) : ZMod p :=
  genericAddXFromSlope E P Q (genericAddSlope E P Q)

/-- Generic affine-addition `y` coordinate in short-Weierstrass form. -/
def genericAddY (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P Q : AffinePoint E) : ZMod p :=
  genericAddYFromSlope E P Q (genericAddSlope E P Q)

/-- The local generic-addition slope agrees with Mathlib's affine slope. -/
theorem genericAddSlope_eq_mathlib (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P Q : AffinePoint E) (_hx : P.x ≠ Q.x) :
    genericAddSlope E P Q =
      E.toWeierstrassCurve.toAffine.slope P.x Q.x P.y Q.y := by
  rfl

/-- The generic-addition slope expands to the source secant quotient
`(y₁ - y₂)/(x₁ - x₂)` in the nonexceptional affine branch. -/
theorem genericAddSlope_eq_secant_quotient
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P Q : AffinePoint E) (hx : GenericAddDomain P Q) :
    genericAddSlope E P Q = genericAddNumerator P Q / genericAddDenominator P Q := by
  rw [genericAddSlope, WeierstrassCurve.Affine.slope_of_X_ne hx]
  rfl


/-- The local generic-addition `x` coordinate agrees with Mathlib's formula. -/
theorem genericAddX_eq_mathlib (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P Q : AffinePoint E) (_hx : P.x ≠ Q.x) :
    genericAddX E P Q =
      E.toWeierstrassCurve.toAffine.addX P.x Q.x
        (E.toWeierstrassCurve.toAffine.slope P.x Q.x P.y Q.y) := by
  rfl

/-- The local generic-addition `y` coordinate agrees with Mathlib's formula. -/
theorem genericAddY_eq_mathlib (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P Q : AffinePoint E) (_hx : P.x ≠ Q.x) :
    genericAddY E P Q =
      E.toWeierstrassCurve.toAffine.addY P.x Q.x P.y
        (E.toWeierstrassCurve.toAffine.slope P.x Q.x P.y Q.y) := by
  rfl

/-- The generic affine-addition output is a nonsingular point. -/
theorem genericAdd_nonsingular (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P Q : AffinePoint E) (hx : P.x ≠ Q.x) :
    E.toWeierstrassCurve.toAffine.Nonsingular
      (genericAddX E P Q) (genericAddY E P Q) := by
  simpa [genericAddX, genericAddY, genericAddXFromSlope, genericAddYFromSlope,
    genericAddSlope] using
    WeierstrassCurve.Affine.nonsingular_add
      (W := E.toWeierstrassCurve.toAffine)
      P.nonsingular Q.nonsingular (fun hxy => hx hxy.1)

/-- The generic affine-addition formula agrees with Mathlib's group law. -/
theorem genericAdd_group_law_mathlib (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P Q : AffinePoint E) (hx : P.x ≠ Q.x) :
    P.toMathlib + Q.toMathlib =
      WeierstrassCurve.Affine.Point.some
        (genericAddX E P Q) (genericAddY E P Q)
        (genericAdd_nonsingular E P Q hx) := by
  simpa [AffinePoint.toMathlib, genericAddX, genericAddY, genericAddXFromSlope,
    genericAddYFromSlope, genericAddSlope] using
    WeierstrassCurve.Affine.Point.add_of_X_ne
      (W := E.toWeierstrassCurve.toAffine)
      (h₁ := P.nonsingular) (h₂ := Q.nonsingular) hx

/-- The generic affine-addition output packaged as a circuit-facing affine
point, using the generic affine endpoint formula [PZ03, ecc.tex:525-640]. -/
def genericAddPoint (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P Q : AffinePoint E) (h : GenericAddDomain P Q) : AffinePoint E where
  x := genericAddX E P Q
  y := genericAddY E P Q
  nonsingular := genericAdd_nonsingular E P Q h

@[simp] theorem genericAddPoint_x (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P Q : AffinePoint E) (h : GenericAddDomain P Q) :
    (genericAddPoint E P Q h).x = genericAddX E P Q :=
  rfl

@[simp] theorem genericAddPoint_y (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P Q : AffinePoint E) (h : GenericAddDomain P Q) :
    (genericAddPoint E P Q h).y = genericAddY E P Q :=
  rfl

namespace AffinePoint

/-- The finite affine inverse of a nonsingular point. -/
public def negate {E : PrimeFieldShortWeierstrass p}
    (P : AffinePoint E) : AffinePoint E where
  x := P.x
  y := E.toWeierstrassCurve.toAffine.negY P.x P.y
  nonsingular :=
    (WeierstrassCurve.Affine.nonsingular_neg
      (W' := E.toWeierstrassCurve.toAffine) P.x P.y).mpr P.nonsingular

/-- Affine negation preserves the finite `x` coordinate. -/
@[simp] theorem negate_x {E : PrimeFieldShortWeierstrass p}
    (P : AffinePoint E) : (negate P).x = P.x :=
  rfl

/-- Affine negation replaces the finite `y` coordinate by Mathlib's negated ordinate. -/
@[simp] theorem negate_y {E : PrimeFieldShortWeierstrass p}
    (P : AffinePoint E) :
    (negate P).y = E.toWeierstrassCurve.toAffine.negY P.x P.y :=
  rfl

/-- The finite affine inverse remains nonsingular. -/
theorem negate_nonsingular {E : PrimeFieldShortWeierstrass p}
    (P : AffinePoint E) :
    E.toWeierstrassCurve.toAffine.Nonsingular (negate P).x (negate P).y :=
  (negate P).nonsingular

/-- The finite affine inverse agrees with the Mathlib group inverse. -/
@[simp] theorem negate_toMathlib {E : PrimeFieldShortWeierstrass p}
    (P : AffinePoint E) : (negate P).toMathlib = -P.toMathlib :=
  rfl

/-- Applying finite affine negation twice restores the original point. -/
@[simp] theorem negate_negate {E : PrimeFieldShortWeierstrass p}
    (P : AffinePoint E) : negate (negate P) = P := by
  apply ext_coordinates
  · rfl
  · exact WeierstrassCurve.Affine.negY_negY
      (W' := E.toWeierstrassCurve.toAffine) P.x P.y

/-- Generic-addition domain checks are unchanged when only the addend is negated. -/
@[simp] theorem genericAddDomain_negate_iff {E : PrimeFieldShortWeierstrass p}
    (P Q : AffinePoint E) :
    GenericAddDomain P (negate Q) ↔ GenericAddDomain P Q :=
  Iff.rfl

end AffinePoint

/-- Distinctness from a fixed affine point and its inverse is exactly the
published nonexceptional boundary needed by the generic secant circuit. -/
theorem genericAddDomain_of_ne_of_ne_negate
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P Q : AffinePoint E) (hPQ : P ≠ Q)
    (hPnegQ : P ≠ AffinePoint.negate Q) :
    GenericAddDomain P Q := by
  intro hx
  have hy :=
    WeierstrassCurve.Affine.Y_eq_of_X_eq
      (W := E.toWeierstrassCurve.toAffine)
      P.nonsingular.1 Q.nonsingular.1 hx
  rcases hy with hy | hy
  · exact hPQ (AffinePoint.ext_coordinates P Q hx hy)
  · apply hPnegQ
    exact AffinePoint.ext_coordinates P (AffinePoint.negate Q)
      (by simpa using hx) (by simpa using hy)

/-- Nonexceptional affine-doubling slope in short-Weierstrass form. -/
def doubleSlope (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P : AffinePoint E) : ZMod p :=
  E.toWeierstrassCurve.toAffine.slope P.x P.x P.y P.y

/-- The short-Weierstrass tangent slope
`λ = (3*x^2 + a)/(2*y)` for a nonexceptional doubling input. -/
def doubleLambda (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P : AffinePoint E) : ZMod p :=
  ((3 : ZMod p) * P.x ^ 2 + E.a) / ((2 : ZMod p) * P.y)

/-- Nonexceptional affine-doubling `x` coordinate. -/
def doubleX (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P : AffinePoint E) : ZMod p :=
  E.toWeierstrassCurve.toAffine.addX P.x P.x (doubleSlope E P)

/-- Nonexceptional affine-doubling `y` coordinate. -/
def doubleY (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P : AffinePoint E) : ZMod p :=
  E.toWeierstrassCurve.toAffine.addY P.x P.x P.y (doubleSlope E P)

/-- The short-form condition `2y ≠ 0` excludes the vertical tangent case. -/
theorem ne_negY_of_two_mul_ne_zero (E : PrimeFieldShortWeierstrass p)
    (P : AffinePoint E) (h2y : (2 : ZMod p) * P.y ≠ 0) :
    P.y ≠ E.toWeierstrassCurve.toAffine.negY P.x P.y := by
  intro hy
  have hneg : E.toWeierstrassCurve.toAffine.negY P.x P.y = -P.y := by
    simp [toWeierstrassCurve, WeierstrassCurve.Affine.negY]
  rw [hneg] at hy
  apply h2y
  calc
    (2 : ZMod p) * P.y = P.y + P.y := by ring
    _ = P.y + -P.y := by
      nth_rewrite 2 [hy]
      rfl
    _ = 0 := by simp

/-- The local doubling slope agrees with Mathlib's tangent slope. -/
theorem doubleSlope_eq_mathlib (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P : AffinePoint E) (_h2y : (2 : ZMod p) * P.y ≠ 0) :
    doubleSlope E P =
      E.toWeierstrassCurve.toAffine.slope P.x P.x P.y P.y := by
  rfl

/-- The doubling slope expands to the usual short-Weierstrass formula. -/
theorem doubleSlope_eq_short_formula (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P : AffinePoint E) (h2y : (2 : ZMod p) * P.y ≠ 0) :
    doubleSlope E P = doubleLambda E P := by
  have hy := ne_negY_of_two_mul_ne_zero E P h2y
  rw [doubleSlope]
  rw [WeierstrassCurve.Affine.slope_of_Y_ne
    (W := E.toWeierstrassCurve.toAffine)
    (x₁ := P.x) (x₂ := P.x) (y₁ := P.y) (y₂ := P.y) rfl hy]
  simp [doubleLambda, toWeierstrassCurve, WeierstrassCurve.Affine.negY]
  ring

/-- The local doubling `x` coordinate agrees with Mathlib's formula. -/
theorem doubleX_eq_mathlib (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P : AffinePoint E) (_h2y : (2 : ZMod p) * P.y ≠ 0) :
    doubleX E P =
      E.toWeierstrassCurve.toAffine.addX P.x P.x
        (E.toWeierstrassCurve.toAffine.slope P.x P.x P.y P.y) := by
  rfl

/-- The doubled `x` coordinate expands to `λ^2 - 2*x`. -/
theorem doubleX_eq_short_formula (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P : AffinePoint E) (h2y : (2 : ZMod p) * P.y ≠ 0) :
    doubleX E P = doubleLambda E P ^ 2 - (2 : ZMod p) * P.x := by
  rw [doubleX, doubleSlope_eq_short_formula E P h2y]
  simp [doubleLambda, toWeierstrassCurve, WeierstrassCurve.Affine.addX]
  ring

/-- The local doubling `y` coordinate agrees with Mathlib's formula. -/
theorem doubleY_eq_mathlib (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P : AffinePoint E) (_h2y : (2 : ZMod p) * P.y ≠ 0) :
    doubleY E P =
      E.toWeierstrassCurve.toAffine.addY P.x P.x P.y
        (E.toWeierstrassCurve.toAffine.slope P.x P.x P.y P.y) := by
  rfl

/-- The doubled `y` coordinate expands to `λ*(x - x₃) - y`, where
`x₃ = λ^2 - 2*x`. -/
theorem doubleY_eq_short_formula (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P : AffinePoint E) (h2y : (2 : ZMod p) * P.y ≠ 0) :
    doubleY E P =
      doubleLambda E P *
        (P.x - (doubleLambda E P ^ 2 - (2 : ZMod p) * P.x)) - P.y := by
  rw [doubleY, doubleSlope_eq_short_formula E P h2y]
  simp [doubleLambda, toWeierstrassCurve, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.negY]
  ring

/-- The nonexceptional doubling output is a nonsingular point. -/
theorem double_nonsingular (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P : AffinePoint E) (h2y : (2 : ZMod p) * P.y ≠ 0) :
    E.toWeierstrassCurve.toAffine.Nonsingular
      (doubleX E P) (doubleY E P) := by
  have hy := ne_negY_of_two_mul_ne_zero E P h2y
  simpa [doubleX, doubleY, doubleSlope] using
    WeierstrassCurve.Affine.nonsingular_add
      (W := E.toWeierstrassCurve.toAffine)
      P.nonsingular P.nonsingular (fun hxy => hy hxy.2)

/-- The nonexceptional affine-doubling formula agrees with Mathlib's group law. -/
theorem double_group_law_mathlib (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P : AffinePoint E) (h2y : (2 : ZMod p) * P.y ≠ 0) :
    P.toMathlib + P.toMathlib =
      WeierstrassCurve.Affine.Point.some
        (doubleX E P) (doubleY E P) (double_nonsingular E P h2y) := by
  have hy := ne_negY_of_two_mul_ne_zero E P h2y
  simpa [AffinePoint.toMathlib, doubleX, doubleY, doubleSlope] using
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne
      (W := E.toWeierstrassCurve.toAffine)
      (h₁ := P.nonsingular) hy


end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
