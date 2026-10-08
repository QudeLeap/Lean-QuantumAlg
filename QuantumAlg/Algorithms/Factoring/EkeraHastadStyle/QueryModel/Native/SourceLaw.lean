/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Encoding
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Distribution

/-!
# Original-width group-query source law

The source Born outcome distribution is independent of the faithful target
encoding. It agrees with the prepared mathematical sample law while keeping
its actual declared execution and resource accounting separate.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native

noncomputable section

/-- The original-width XOR member has the already accepted source exponent law. -/
theorem source_outcomePMF_eq_selected {N : Nat} (input : Input N)
    (parameter : (ParameterShape N).Value) :
    (ShortDLP.measurement (parameters N)).outcomePMF
      (ShortDLP.BornProbability.evolvedState (encoding input)
        (parameterUnit parameter) (parameterTarget parameter)) = selectedOutcomePMF parameter := by
  let : NeZero N := ⟨Nat.ne_of_gt input.modulus_pos⟩
  unfold selectedOutcomePMF
  rw [dif_pos (show 1 < N ∧ N < 2 ^ arithmeticBits N from
    ⟨input.modulus_gt_one, modulus_lt_arithmeticCapacity N⟩)]
  apply PMF.ext
  intro outcome
  obtain ⟨label, rfl⟩ :=
    (ShortDLP.BornProbability.shortDLPMeasurementOutcome_bijective
      (parameters N)).surjective outcome
  obtain ⟨pair, rfl⟩ := prodEquiv.surjective label
  have independent := pairBornProbability_encoding_independent (shortLogBits N) (tradeoffBits N)
    (encoding input)
    (ShortDLP.CompiledMAU.unitEncoding (arithmeticBits N) N input.modulus_gt_one
      (modulus_lt_arithmeticCapacity N)) (parameterUnit parameter) (parameterTarget parameter) pair
  exact (ShortDLP.BornProbability.shortDLPBornOutcomeProbability_eq_pairBornProbability
    (encoding input) (parameterUnit parameter) (parameterTarget parameter) pair).trans
    (independent.trans
      (ShortDLP.BornProbability.shortDLPBornOutcomeProbability_eq_pairBornProbability
        (params := ShortDLP.CompiledMAU.registerParameters
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N))
        (ShortDLP.CompiledMAU.unitEncoding (arithmeticBits N) N input.modulus_gt_one
          (modulus_lt_arithmeticCapacity N))
        (parameterUnit parameter) (parameterTarget parameter) pair).symm)


end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native
