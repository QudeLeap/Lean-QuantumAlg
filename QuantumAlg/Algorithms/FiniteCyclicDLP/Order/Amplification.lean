/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Probability
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Amplification.Model
public import QuantumAlg.Util.PMF
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Amplification.Model
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Probability
import all QuantumAlg.Util.PMF
import Mathlib.Data.Vector.Mem

/-!
# Two-thirds amplification of the native-dimensional sampler

The conservative source retry count amplifies the selected Fourier family of
the actual all-order circuit.  This layer concerns independent repetitions of
the one-cycle Born law; execution and recovery are connected separately.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderAmplification

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G] [Fintype G]

private lemma selected_probability (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) (secret : FiniteCyclicDLP.Input P) :
    Probability.selectedOutcomeFamilyLowerBound P ≤
      (OrderBornBridge.outcomePMF P expansion).toOuterMeasure
        {outcome | Probability.SelectedOutcome P secret outcome} := by
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  have lower :=
    OrderProbability.selectedOutcomeFamilyLowerBound_le_bornSelectedProbability
      secret expansion
  convert lower using 1
  congr 1
  ext outcome
  simp only [Set.mem_ofPred_eq, Probability.SelectedOutcome,
    FiniteCyclicDLP.Probability.selectedOutcomeFamily,
    Canonical.Probability.selectedRawOutcomeFamily, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨unit, same⟩
    exact ⟨unit, same.symm⟩
  · rintro ⟨unit, same⟩
    exact ⟨unit, same.symm⟩

/-- The original conservative retry count gives selected recoverable data with
probability at least two thirds for every positive finite cyclic order. -/
public lemma selected_vector_probability (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) (secret : FiniteCyclicDLP.Input P) :
    ENNReal.ofReal ((2 : Real) / 3) ≤
      (PMF.independentReplicateVector (OrderBornBridge.outcomePMF P expansion)
        (FiniteCyclicDLP.Canonical.retryCount P)).toOuterMeasure
        {outcomes |
          ∃ index, Probability.SelectedOutcome P secret (outcomes.get index)} := by
  have amplified := PMF.independentReplicate_successProbability_ge
    (OrderBornBridge.outcomePMF P expansion)
    (Probability.SelectedOutcome P secret)
    (FiniteCyclicDLP.Canonical.retryCount P)
    (Probability.selectedOutcomeFamilyLowerBound P)
    (ENNReal.ofReal ((2 : Real) / 3))
    (selected_probability P expansion secret) (by
      rw [FiniteCyclicDLP.Canonical.one_sub_selectedRawOutcomeFamilyLowerBound_eq_sourceFailure]
      exact FiniteCyclicDLP.Canonical.twoThirds_le_one_sub_retryFailurePower P)
  rw [← PMF.independentReplicateVector_toList, PMF.toOuterMeasure_map_apply] at amplified
  have events :
      {outcomes : List.Vector
          (TerminalZMeasure.Outcome
            (OrderPreparation.width P + OrderPreparation.width P))
          (FiniteCyclicDLP.Canonical.retryCount P) |
        PMF.ContainsEvent (Probability.SelectedOutcome P secret) outcomes.toList} =
      {outcomes |
        ∃ index, Probability.SelectedOutcome P secret (outcomes.get index)} := by
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

end QuantumAlg.FiniteCyclicDLP.OrderAmplification
