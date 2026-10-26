/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Field.Columns
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Finish.Correctness

/-!
# The same curve and five columns at an equal modulus

Equality of the original modulus with a symbolic target transports the
original curve and its same affine point together. Natural-value casts
of all five original table columns are then the mathematical columns of
that point. The exceptional column keeps its original total quotient.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition

noncomputable section

open ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve.WindowTables

/-- The original complete curve certificate at the equal target modulus. -/
def curveAtModulus {width : Nat} (spec : CurveSpec width) {target : Nat}
    (sameModulus : spec.field.modulus = target) : PrimeFieldShortWeierstrass target :=
  sameModulus ▸ spec.curve

/-- The same original affine point on that transported complete curve. -/
def affineAtModulus {width : Nat} (spec : CurveSpec width) {target : Nat}
    (sameModulus : spec.field.modulus = target) (point : AffinePoint spec.curve) :
    AffinePoint (curveAtModulus spec sameModulus) := by
  cases sameModulus
  exact point

/-- All five natural-value casts are the same transported point's mathematical columns. -/
lemma fiveColumns_cast_modulus {width : Nat} (spec : CurveSpec width) (target : Nat)
    (sameModulus : spec.field.modulus = target) (point : AffinePoint spec.curve)
    (column : Fin 5) :
    let curve := curveAtModulus spec sameModulus
    let selected := affineAtModulus spec sameModulus point
    letI : Fact target.Prime := ⟨curve.prime⟩
    ((fiveColumns spec point.x point.y column).val : ZMod target) =
      ![-selected.x, -selected.y, 3 * selected.x,
        -exceptionalSlope curve selected, selected.x + 1] column := by
  subst target
  change ((fiveColumns spec point.x point.y column).val : ZMod spec.field.modulus) =
    ![-point.x, -point.y, 3 * point.x,
      -exceptionalSlope spec.curve point, point.x + 1] column
  rw [ZMod.natCast_zmod_val]
  simp only [fiveColumns, windowTables_exceptionalSlope_eq]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
