/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Classical.EllipticCurve
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Original fitted public elliptic-curve specification

The original coordinate width, fitted field and ellipticity proof are pure
mathematical data. Their names and bodies remain unchanged independently of
the retired executable ECDLP layout and recovery backend.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.Layout

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

namespace FixedEC

/-- Fixed-width curve specification used by the intrinsic ECDLP point code. -/
abbrev CurveSpec := ClassicalAlgorithms.EllipticCurve.CurveSpec
end FixedEC

/-- Canonical bit width of one prime-field coordinate.  The curve argument
keeps the width API aligned with the curve-specific coordinate carriers. -/
@[nolint unusedArguments]
def fieldWidth (_E : PrimeFieldShortWeierstrass p) : Nat :=
  Nat.clog 2 p

/-- The prime modulus fits its canonical coordinate width. -/
theorem field_modulus_le_capacity (E : PrimeFieldShortWeierstrass p) :
    p ≤ ClassicalAlgorithms.modulus (fieldWidth E) := by
  simpa [fieldWidth, ClassicalAlgorithms.modulus] using
    (Nat.le_pow_clog (by norm_num : 1 < 2) p)

/-- Fixed-width field data derived from the curve itself. -/
def fieldSpec (E : PrimeFieldShortWeierstrass p) :
    ClassicalAlgorithms.Modular.ModulusSpec (fieldWidth E) where
  modulus := p
  two_le := by
    have characteristicBound := E.three_lt
    omega
  le_capacity := field_modulus_le_capacity E

/-- Every certified short-Weierstrass curve in the ECDLP model supplies the
Mathlib ellipticity witness needed by the complete point representation. -/
theorem curveIsElliptic (E : PrimeFieldShortWeierstrass p) :
    E.toWeierstrassCurve.toAffine.IsElliptic where
  isUnit := by
    let _ : Fact p.Prime := ⟨E.prime⟩
    let _ : E.toWeierstrassCurve.toAffine.IsShortNF :=
      { a₁ := rfl
        a₂ := rfl
        a₃ := rfl }
    apply isUnit_iff_ne_zero.mpr
    rw [WeierstrassCurve.Δ_of_isShortNF]
    apply mul_ne_zero
    · apply neg_ne_zero.mpr
      intro sixteenZero
      have dividesSixteen : p ∣ 16 :=
        (ZMod.natCast_eq_zero_iff 16 p).mp sixteenZero
      have dividesTwo : p ∣ 2 := by
        have dividesPower : p ∣ 2 ^ 4 := by
          norm_num
          exact dividesSixteen
        exact E.prime.dvd_of_dvd_pow dividesPower
      have pLeTwo := Nat.le_of_dvd (by norm_num : 0 < 2) dividesTwo
      have characteristicBound := E.three_lt
      omega
    · simpa [PrimeFieldShortWeierstrass.toWeierstrassCurve] using
        E.nonsingular

/-- The complete fixed-width curve specification derived from the mathematical
ECDLP curve; no implementation parameter is exposed. -/
def curveSpec (E : PrimeFieldShortWeierstrass p) : FixedEC.CurveSpec (fieldWidth E) where
  field := fieldSpec E
  curve := E
  elliptic := curveIsElliptic E

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.Layout
