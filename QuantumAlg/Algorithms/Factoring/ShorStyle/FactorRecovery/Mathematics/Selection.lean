/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Mathematics

/-!
# Original source selection in the real stored-guard form

This is an equality of the original mathematical selector. It separates the
known-modulus exception from the actual sampler priority and the accepted,
positive-even order test, without changing any sample or arithmetic domain.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

noncomputable section

/-- Outside the modulus exception, the source uses exactly the actual guard predicates. -/
theorem outputOfResidue_guard {N : Nat}
    (parameter : CShape.Value (ParameterShape (modulusBits N))) (accepted : Bool)
    (order : ClassicalAlgorithms.Word (phaseBits N + 1))
    (ordinary : ¬ (2 < N ∧ Even N)) :
    outputOfResidue (N := N) parameter accepted order =
      if parameter.second.first.toBool then some parameter.second.second.toNat
      else if accepted = true ∧ 0 < order.val ∧ Even order.val then
        factorFromHalfPowerValue N (parameter.first.toNat ^ (order.val / 2) % N)
      else none := by
  by_cases early : parameter.second.first.toBool = true
  · simp [outputOfResidue, ordinary, early]
  · cases accepted <;>
      simp [outputOfResidue, factorFromOrderResidueValue, ordinary, early]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
