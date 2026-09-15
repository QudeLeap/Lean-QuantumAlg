/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Classical.NumberTheory.Euclidean

/-!
# Width-only residue-sampler arithmetic

This numerical bound is independent of an execution representation. Its
same-bit arithmetic specializations use the original Euclidean fuel and
public word width.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler

/-- Original scalar allowance for proposal decoding, selection and the Euclidean seam. -/
def samplerClassicalBound (width : Nat) : Nat :=
  5 * ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel (width + 1) +
    34 * width + 163

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler
