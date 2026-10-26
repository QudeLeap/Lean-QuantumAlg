/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Residue.Input

/-!
# The original arithmetic domain for a nonzero ordinary field coordinate

Primality and nonzero X discharge precisely the existing resident call's
positive, bounded and coprime input obligations. Canonical Y is the same
ordinary field word. No extra denominator or reverse-domain condition is
introduced for the point operation's reachable exceptional branch.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call.Endpoint

noncomputable section

/-- Nonzero field X satisfies the original selected arithmetic domain. -/
lemma activeDomain_residue [Fact modulus.Prime] (x y : ZMod modulus) (nonzero : x ≠ 0) :
    ActiveDomain (Residue.input x) (Residue.input y) where
  coprime := Residue.input_coprime x nonzero
  positive := Residue.input_positive x nonzero
  bounded := Residue.input_bounded x
  canonical := Residue.input_bounded y

end

end Arithmetic.Call.Endpoint

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
