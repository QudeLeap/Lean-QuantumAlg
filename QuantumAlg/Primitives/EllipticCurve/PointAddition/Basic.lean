/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Mathematics
import all QuantumAlg.Primitives.MAU.Division

/-!
# Unit-denominator division inputs for affine addition

These existing adapters connect the independent affine formulas to the
unit-denominator division interface [PZ03, ecc.tex:525-640]. All field and
point mathematics belongs to the separate mathematics owner.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass

variable {p : ℕ}

/-- A clean modular-division input shape for generic affine-addition slope
denominators. -/
def genericAddDivisionData {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (P Q : AffinePoint E) (h : GenericAddDomain P Q)
    (numerator target : ZMod p) : MAU.Division.Data p where
  denominator := genericAddDenominatorUnit P Q h
  numerator := numerator
  target := target
  flag := false


/-- A clean modular-division input shape for affine-doubling tangent
denominators. -/
def doubleDivisionData {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (P : AffinePoint E) (h : GenericDoubleDomain P)
    (numerator target : ZMod p) : MAU.Division.Data p where
  denominator := doubleDenominatorUnit P h
  numerator := numerator
  target := target
  flag := false


/-- The modular-division primitive computes the generic affine-addition slope
when it is loaded with the source numerator and unit denominator. -/
theorem genericAddSlope_eq_quotientResidue
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (P Q : AffinePoint E) (hx : GenericAddDomain P Q) :
    MAU.Division.quotientResidue (genericAddDenominatorUnit P Q hx)
        (genericAddNumerator P Q) =
      genericAddSlope E P Q := by
  rw [genericAddSlope_eq_secant_quotient E P Q hx]
  simp [MAU.Division.quotientResidue, MAU.Inversion.inverseResidue,
    genericAddDenominatorUnit, genericAddDenominator, genericAddNumerator,
    div_eq_mul_inv]

end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
