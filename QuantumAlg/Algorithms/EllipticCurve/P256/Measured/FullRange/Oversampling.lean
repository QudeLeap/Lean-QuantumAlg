/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Cascade.Parameters
import Mathlib.Tactic.NormNum

/-!
# The original P-256 exponent width has the full-range sampling reserve

This is the existing numerical oversampling fact for the unchanged public-key
instance and its original known-order problem. It depends only on mathematical
parameters, independently of either measured execution backend.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.FullRange

noncomputable section

open PrimeFieldShortWeierstrass

/-- The complete physical power-of-two grid has at least sixteen samples per cyclic character. -/
lemma fullRange_oversampling (I : DomainParameters.PublicKeyInstance) :
    16 * (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).order ≤
      2 ^ Cascade.exponentWidth I := by
  change 16 * DomainParameters.subgroupOrder ≤ 2 ^ Cascade.exponentWidth I
  rw [Cascade.exponentWidth_eq_260]
  rw [show 260 = 256 + 4 by decide, pow_add]
  norm_num [DomainParameters.subgroupOrder]

end

end QuantumAlg.EllipticCurve.P256.Measured.FullRange
