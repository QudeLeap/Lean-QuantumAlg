/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Placement.Geometry
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Placement

/-!
# Actual measured body at the selected exponent position

The real point body uses the exact injective physical and storage maps of the
indexed workspace. The maps preserve every original arithmetic address.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open MeasuredUncompute

/-- The actual selected body rewrites native addresses and finite operands with these exact maps. -/
def body {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (MeasuredPointAddition.Placement.context p.size (storageMap p.size active)
        (physicalMap p.size active))
      (MeasuredPointAddition.Placement.context p.size (storageMap p.size active)
        (physicalMap p.size active)) :=
  MeasuredPointAddition.Placement.body E Q (storageMap p.size active) (physicalMap p.size active)

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
