/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Input
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Amplification.Model
import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Born
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Probability
import Mathlib.Data.Vector.Mem

/-!
# Original selected-family amplification at the original retry count

The unchanged concrete Born floor and conservative calibration concern only
the original group and source circuit. Actual sample and recovery semantics
are connected by the complete endpoint.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint

open GateLevelAttempt.Native (sampleWidth)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G]

private theorem selected_probability (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    (secret : Probability.SecretInput P) :
    Probability.selectedRawOutcomeFamilyLowerBound P ≤
      (GateLevelAttempt.Native.outcomePMF P B A.ux).toOuterMeasure
        {outcome | Probability.SelectedRawOutcome P secret outcome} := by
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  rw [GateLevelAttempt.Native.nativeFiniteCyclic_outcomePMF_eq_concrete]
  have lower := Concrete.Probability.selectedOutcomeFamilyLowerBound_le_bornSelectedProbability
    secret (circuitAccess P B A.ux)
  convert lower using 1
  congr 1
  ext outcome
  simp only [Set.mem_ofPred_eq, Probability.SelectedRawOutcome,
    FiniteCyclicDLP.Probability.selectedOutcomeFamily, Probability.selectedRawOutcomeFamily,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨unit, same⟩
    exact ⟨unit, same.symm⟩
  · rintro ⟨unit, same⟩
    exact ⟨unit, same.symm⟩

/-- The original conservative count amplifies the original selected Fourier family. -/
theorem finiteCyclic_selected_vector_probability (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    (secret : Probability.SecretInput P) :
    ENNReal.ofReal ((2 : Real) / 3) ≤
      (PMF.independentReplicateVector (GateLevelAttempt.Native.outcomePMF P B A.ux)
        (retryCount P)).toOuterMeasure
        {outcomes | ∃ index, Probability.SelectedRawOutcome P secret (outcomes.get index)} := by
  have amplified := PMF.independentReplicate_successProbability_ge
    (GateLevelAttempt.Native.outcomePMF P B A.ux) (Probability.SelectedRawOutcome P secret)
    (retryCount P) (Probability.selectedRawOutcomeFamilyLowerBound P)
    (ENNReal.ofReal ((2 : Real) / 3)) (selected_probability P B A secret) (by
      rw [one_sub_selectedRawOutcomeFamilyLowerBound_eq_sourceFailure]
      exact twoThirds_le_one_sub_retryFailurePower P)
  rw [← PMF.independentReplicateVector_toList, PMF.toOuterMeasure_map_apply] at amplified
  have events :
      {outcomes : List.Vector (Fin (sampleWidth P) → Bool) (retryCount P) |
        PMF.ContainsEvent (Probability.SelectedRawOutcome P secret) outcomes.toList} =
      {outcomes | ∃ index, Probability.SelectedRawOutcome P secret (outcomes.get index)} := by
    ext outcomes
    constructor
    · rintro ⟨outcome, member, selected⟩
      obtain ⟨index, same⟩ := (List.Vector.mem_iff_get outcome outcomes).mp member
      exact ⟨index, same.symm ▸ selected⟩
    · rintro ⟨index, selected⟩
      exact ⟨outcomes.get index, List.Vector.get_mem index outcomes, selected⟩
  rw [← events]
  exact amplified

end

end QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint
