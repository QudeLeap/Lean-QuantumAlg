/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Field
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Domain

/-!
# The original table exceptional column and the measured field constant

Both constants use the same total secant quotient through the doubled
negative point. The fixed-width curve already supplies its prime-field
certificate. This comparison needs no nonzero denominator, tangent-domain
or additional point exclusion, and is independent of the word width.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition

noncomputable section

open ClassicalAlgorithms.EllipticCurve

private lemma table_doubleX_negate {width : Nat} (spec : CurveSpec width)
    (point : AffinePoint spec.curve) :
    ShortWeierstrass.doubleX spec point.x (-point.y) =
      doubleX spec.curve (AffinePoint.negate point) := by
  rw [ShortWeierstrass.doubleX_eq_mathlib]
  simp only [doubleX, doubleSlope, ShortWeierstrass.doubleSlope,
    AffinePoint.negate_x, AffinePoint.negate_y,
    ShortWeierstrass.mathlib_negY_eq_negY, ShortWeierstrass.negY]

private lemma table_doubleY_negate {width : Nat} (spec : CurveSpec width)
    (point : AffinePoint spec.curve) :
    ShortWeierstrass.doubleY spec point.x (-point.y) =
      doubleY spec.curve (AffinePoint.negate point) := by
  rw [ShortWeierstrass.doubleY_eq_mathlib]
  simp only [doubleY, doubleSlope, ShortWeierstrass.doubleSlope,
    AffinePoint.negate_x, AffinePoint.negate_y,
    ShortWeierstrass.mathlib_negY_eq_negY, ShortWeierstrass.negY]

/-- The actual table specification uses the same total exceptional field constant. -/
lemma windowTables_exceptionalSlope_eq {width : Nat} (spec : CurveSpec width)
    (point : AffinePoint spec.curve) :
    ClassicalRoutines.EllipticCurve.WindowTables.exceptionalSlope spec point.x point.y =
      exceptionalSlope spec.curve point := by
  rw [ClassicalRoutines.EllipticCurve.WindowTables.exceptionalSlope, exceptionalSlope,
    table_doubleY_negate, table_doubleX_negate]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
