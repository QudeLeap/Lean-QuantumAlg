/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Encoding
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Layout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Layout

/-!
# Encoding-independent exponent probabilities at the original widths

The original oracle target and compiled arithmetic workspace give the same
exponent-pair marginal. Their circuits and resource budgets remain distinct.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel

noncomputable section

/-- The original oracle and wider compiled encoding have the same exponent-pair marginal. -/
lemma pairBornProbability_eq_compiled {N : Nat} (input : Input N)
    (g x : (ZMod N)ˣ)
    (pair : Fin (2 ^ ShortDLP.firstBits (Native.parameters N)) ×
      Fin (2 ^ (Native.parameters N).ell)) :
    ShortDLP.BornProbability.pairBornProbability (Native.encoding input) g x pair =
      ShortDLP.BornProbability.pairBornProbability
        (params := ShortDLP.CompiledMAU.registerParameters
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N))
        (ShortDLP.CompiledMAU.unitEncoding (arithmeticBits N) N input.modulus_gt_one
          (modulus_lt_arithmeticCapacity N)) g x pair := by
  let _ : NeZero N := input.neZero
  exact pairBornProbability_encoding_independent
    (shortLogBits N) (tradeoffBits N) (Native.encoding input)
    (ShortDLP.CompiledMAU.unitEncoding (arithmeticBits N) N input.modulus_gt_one
      (modulus_lt_arithmeticCapacity N)) g x pair

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel
