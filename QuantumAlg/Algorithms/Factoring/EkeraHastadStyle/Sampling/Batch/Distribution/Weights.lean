/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Distribution
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Moments.Sampled
import all QuantumAlg.Util.PMF.FiniteWeights
import Mathlib.Data.ENNReal.Inv

/-!
# Exact finite weights of the original complete batch PMF

The original uniform-source and conditional-vector distribution has precisely
the nested finite sum appearing in the actual execution's full-reference
identity. Characteristic weights therefore yield its exact point probabilities.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The independent complete source PMF has the exact nested weight derived by the native batch. -/
theorem nativeBatch_sourceDistribution_weighted {N : Nat} (input : Input N)
    (weight : (resultShape N).Value → ℂ) :
    (∑ output : (resultShape N).Value,
      ((sourceDistribution input output).toReal : ℂ) * weight output) =
      ∑ source : Fin (2 ^ residueSamplingBits N),
        (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
          conditionalMoment
            (fun parameter sample outcomes => weight
              (.product sample (.product parameter (.fixedVector outcomes))))
            (parameterValue input source)
            (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits source)) := by
  unfold sourceDistribution
  rw [PMF.sum_bind_toReal_mul]
  apply Finset.sum_congr rfl
  intro source _
  rw [PMF.sum_map_toReal_mul, PMF.uniformOfFintype_apply, Fintype.card_fin,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.ofReal_inv]
  rfl

/-- A characteristic weight extracts the same source PMF's exact probability of one output. -/
theorem nativeBatch_sourceDistribution_indicator {N : Nat} (input : Input N)
    (selected : (resultShape N).Value) :
    (∑ source : Fin (2 ^ residueSamplingBits N),
      (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
        conditionalMoment
          (fun parameter sample outcomes =>
            (fun output : (resultShape N).Value => if output = selected then 1 else 0)
              (.product sample (.product parameter (.fixedVector outcomes))))
          (parameterValue input source)
          (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits source))) =
      ((sourceDistribution input selected).toReal : ℂ) :=
  (nativeBatch_sourceDistribution_weighted input
    (fun output => if output = selected then 1 else 0)).symm.trans
    (PMF.sum_toReal_indicator (sourceDistribution input) selected)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
