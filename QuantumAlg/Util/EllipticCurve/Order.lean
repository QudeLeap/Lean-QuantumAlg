/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.EllipticCurve
import Mathlib.GroupTheory.OrderOfElement

/-!
# Orders in the original elliptic-curve group representation

The multiplicative group wrapper uses the same Mathlib affine group.
Its element order is therefore the additive order of that exact point.
Finite affine representatives are also determined by their Mathlib value.
All facts remain symbolic in the original curve and modulus.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass

noncomputable section

/-- The original multiplicative wrapper and its same additive point have equal orders. -/
lemma groupPoint_orderOf_eq_addOrderOf {p : Nat} (curve : PrimeFieldShortWeierstrass p)
    (point : GroupPoint curve) :
    letI : Fact p.Prime := ⟨curve.prime⟩
    orderOf point = addOrderOf point.toMathlib := by
  let : Fact p.Prime := ⟨curve.prime⟩
  have same := (groupPointEquiv curve).mulEquiv.orderOf_eq point
  change addOrderOf point.toMathlib = orderOf point at same
  exact same.symm

/-- A finite affine point has the same order under its two original representations. -/
lemma affinePoint_addOrderOf_eq_orderOf {p : Nat} (curve : PrimeFieldShortWeierstrass p)
    (point : AffinePoint curve) :
    letI : Fact p.Prime := ⟨curve.prime⟩
    addOrderOf point.toMathlib = orderOf point.toGroupPoint := by
  let : Fact p.Prime := ⟨curve.prime⟩
  exact (groupPoint_orderOf_eq_addOrderOf curve point.toGroupPoint).symm

namespace AffinePoint

/-- The original Mathlib point value uniquely determines a finite affine representative. -/
lemma toMathlib_injective {p : Nat} (curve : PrimeFieldShortWeierstrass p) :
    Function.Injective (toMathlib (E := curve)) := by
  intro first second same
  have coordinates := WeierstrassCurve.Affine.Point.some.inj same
  exact ext_coordinates first second coordinates.1 coordinates.2

end AffinePoint

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
