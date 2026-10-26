/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.EllipticCurve

/-! # Injectivity of the original affine-to-group representation -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint

noncomputable section

/-- Equality in the original total group carrier retains both finite affine coordinates. -/
lemma toGroupPoint_injective {p : Nat} {E : PrimeFieldShortWeierstrass p} :
    Function.Injective (AffinePoint.toGroupPoint (E := E)) := by
  intro P Q same
  have underlying := congrArg GroupPoint.toMathlib same
  change WeierstrassCurve.Affine.Point.some P.x P.y P.nonsingular =
    WeierstrassCurve.Affine.Point.some Q.x Q.y Q.nonsingular at underlying
  have coordinates := WeierstrassCurve.Affine.Point.some.inj underlying
  exact AffinePoint.ext_coordinates P Q coordinates.1 coordinates.2

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint
