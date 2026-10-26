/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Row

/-!
# Faithful complete labels in the original physical wire coordinates

The caller placement is a basis equivalence, so it cannot identify two
complete raw labels. This retains precisely the original physical collisions.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Parameters

noncomputable section

open Execution

/-- The actual complete physical label retains every component of the original raw label. -/
lemma physicalLabel_injective {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx) :
    Function.Injective parameters.physicalLabel := by
  intro first last same
  exact encoding.encode_injective
    ((QubitLayout.canonical encoding.width).basisEquiv.symm.injective
      ((basisOfEqualWires (QubitLayout.canonical encoding.width).toQuantum
        ctx.quantumLayout parameters.sameWires).injective same))

end

end Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
