/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Mathematics

/-!
# Affine field operations shared by the measured point-addition implementations

These mathematical definitions have no circuit, placement, or runtime dependency.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition

noncomputable section

/-- The original affine domain restricts the active control sector alone. -/
def affineAllowed {p : Nat} {E : PrimeFieldShortWeierstrass p}
    (control : Bool) (P Q : AffinePoint E) : Prop :=
  control = true → P ≠ Q ∧ P ≠ AffinePoint.negate Q

/-- The first preserved operand is the original coordinate difference. -/
def firstDifference {p : Nat} (x xQ : ZMod p) : ZMod p := x - xQ

/-- Canonical field slope; no inverse of the numerator or slope is taken. -/
def slope {p : Nat} [Fact p.Prime] (x y xQ yQ : ZMod p) : ZMod p :=
  (y - yQ) / firstDifference x xQ

/-- The second preserved operand becomes the fixed x coordinate minus the result's x. -/
def secondDifference {p : Nat} [Fact p.Prime] (x y xQ yQ : ZMod p) : ZMod p :=
  firstDifference x xQ + 3 * xQ - slope x y xQ yQ ^ 2

/-- A total classical constant; the reachable exceptional arm supplies its domain internally. -/
def exceptionalSlope {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) : ZMod p :=
  (doubleY E (AffinePoint.negate Q) - Q.y) /
    (doubleX E (AffinePoint.negate Q) - Q.x)

/-- Only a nonzero preserved multiplier activates the second measured arithmetic call. -/
def normalControl {p : Nat} (control : Bool) (difference : ZMod p) : Bool :=
  control && decide (difference ≠ 0)

/-- Independent field output, with a reversible constant subtraction on the exceptional arm. -/
def fieldOutput {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (control : Bool) (x y : ZMod p) : ZMod p × ZMod p :=
  if control then
    let value := slope x y Q.x Q.y
    let difference := secondDifference x y Q.x Q.y
    (Q.x - difference,
      (if difference = 0 then value - exceptionalSlope E Q else difference * value) - Q.y)
  else (x, y)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
