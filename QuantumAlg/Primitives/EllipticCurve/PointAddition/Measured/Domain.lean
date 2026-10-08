/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Layout
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Target.Basis

/-!
# Independent prepared domain for measured affine addition

The supplied active affine point excludes exactly the fixed point and its
inverse. The prescribed arithmetic frame and internal zero selector describe
the support established by actual allocation. This predicate depends only on
the physical basis assembly and independent point mathematics.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition

noncomputable section

open MeasuredUncompute

/-- Prepared support is internal: only active affine inputs carry the original point exclusions. -/
def admissible {p : Nat} (E : PrimeFieldShortWeierstrass p)
    (Q : AffinePoint E) (original : (context p.size).register.Index) : Prop :=
  ∃ (control : Fin 2) (x y : Fin (2 ^ p.size)),
    original = label p.size control 0 (InPlaceTarget.preparedBasis p x y) ∧
      (control = 1 → ∃ P : AffinePoint E,
        x.val = P.x.val ∧ y.val = P.y.val ∧ P ≠ Q ∧ P ≠ AffinePoint.negate Q)
end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
