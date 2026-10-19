/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Amplification.Model
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Probability
public import QuantumAlg.Util.PMF
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Amplification.Model
import all QuantumAlg.Algorithms.Factoring.Common
import all QuantumAlg.Util.PMF
import Mathlib.Data.Vector.Mem

/-!
# Repetition count from the complete selected Fourier family

The native one-sample Born proof already sums all `N` group tails and all
`φ(N)` invertible residues. This implementation calibrates its literal number
of attempts from that full `N φ(N)/(4q²)` floor, including the trivial group.
No weaker one-tail floor is substituted [Sho95, source.tex:1841-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.Binary

open Factoring

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The complete selected-family one-sample floor in the implemented binary widths. -/
@[expose] public def attemptFloor (P : KnownOrderProblem G) : Real :=
  ((P.order * Nat.totient P.order : Nat) : Real) /
    (4 * (2 ^ OrderPreparation.width P) ^ 2 : Nat)

/-- The actual repeat count uses the full proven selected-outcome family. -/
@[expose] public def sampleCount (P : KnownOrderProblem G) : Nat :=
  max 1 (Nat.ceil
    (Real.log ((3 : Real) / 1) /
      Real.log (((4 * (2 ^ OrderPreparation.width P) ^ 2 : Nat) : Real) /
        ((4 * (2 ^ OrderPreparation.width P) ^ 2 -
          P.order * Nat.totient P.order : Nat) : Real))))

private lemma sampleCount_eq_canonical (P : KnownOrderProblem G) :
    sampleCount P = Canonical.retryCountForBudget P FailureBudget.oneThird := by
  simp only [sampleCount, Canonical.retryCountForBudget, FailureBudget.retryCountFor,
    FailureBudget.retryExponentFor, Canonical.sourceFailureBudget,
    Canonical.successDenominator, Canonical.successNumerator, fourierModulus,
    OrderPreparation.width, FailureBudget.oneThird, Nat.cast_ofNat, Nat.cast_one]

/-- The logarithmic exponent is positive for the fixed one-third failure target. -/
private lemma retryExponent_pos (P : KnownOrderProblem G) :
    0 < FailureBudget.retryExponentFor (Canonical.sourceFailureBudget P)
      FailureBudget.oneThird := by
  have valid := Canonical.sourceFailureBudget_strictlyWellFormed P
  have positive : (0 : Real) < (Canonical.sourceFailureBudget P).failureNumerator := by
    exact_mod_cast valid.numerator_pos
  have ratio : 1 <
      ((Canonical.sourceFailureBudget P).failureDenominator : Real) /
        (Canonical.sourceFailureBudget P).failureNumerator := by
    rw [lt_div_iff₀ positive]
    simpa using (show ((Canonical.sourceFailureBudget P).failureNumerator : Real) <
      (Canonical.sourceFailureBudget P).failureDenominator by
        exact_mod_cast valid.numerator_lt_denominator)
  unfold FailureBudget.retryExponentFor
  exact div_pos (by norm_num [FailureBudget.oneThird]; positivity)
    (Real.log_pos ratio)

/-- The internal `max 1` is redundant here; the implemented count is the plain ceiling. -/
private lemma sampleCount_eq_ceil (P : KnownOrderProblem G) :
    sampleCount P = Nat.ceil
      (FailureBudget.retryExponentFor (Canonical.sourceFailureBudget P)
        FailureBudget.oneThird) := by
  have positive := Nat.ceil_pos.mpr (retryExponent_pos P)
  rw [sampleCount_eq_canonical]
  change max 1 (Nat.ceil
    (FailureBudget.retryExponentFor (Canonical.sourceFailureBudget P)
      FailureBudget.oneThird)) = _
  exact Nat.max_eq_right positive

/-- The actual number of attempts is positive at every admitted group order. -/
public lemma sampleCount_pos (P : KnownOrderProblem G) : 0 < sampleCount P := by
  rw [sampleCount_eq_canonical]
  exact FailureBudget.retryCountFor_pos (Canonical.sourceFailureBudget P) FailureBudget.oneThird

/-- The positive reciprocal-log calibration is exactly the signed-log public formula. -/
private lemma sampleCount_eq_signedLog (P : KnownOrderProblem G) :
    sampleCount P = Nat.ceil
      (Real.log ((1 : Real) / 3) / Real.log (1 - Canonical.attemptFloor P)) := by
  rw [sampleCount_eq_ceil]
  apply congrArg Nat.ceil
  rw [← Canonical.sourceFailureBudget_value]
  unfold FailureBudget.retryExponentFor FailureBudget.value
  have reciprocal :
      (((Canonical.sourceFailureBudget P).failureNumerator : Real) /
        (Canonical.sourceFailureBudget P).failureDenominator) =
      (((Canonical.sourceFailureBudget P).failureDenominator : Real) /
        (Canonical.sourceFailureBudget P).failureNumerator)⁻¹ := by
    simp only [inv_div]
  have logThird : Real.log ((1 : Real) / 3) = -Real.log 3 := by
    simpa only [one_div] using Real.log_inv (3 : Real)
  rw [reciprocal, Real.log_inv, logThird]
  simp only [FailureBudget.oneThird, Nat.cast_ofNat, Nat.cast_one, div_one, neg_div_neg_eq]

/-- The displayed power-of-two denominator is the exact full-family denominator. -/
private lemma attemptFloor_eq_width (P : KnownOrderProblem G) :
    Canonical.attemptFloor P =
      ((P.order : Real) * Nat.totient P.order) /
        2 ^ (2 * OrderPreparation.width P + 2) := by
  have denominator : (Canonical.successDenominator P : Real) =
      2 ^ (2 * OrderPreparation.width P + 2) := by
    change ((4 * (2 ^ OrderPreparation.width P) ^ 2 : Nat) : Real) = _
    push_cast
    calc
      (4 : Real) * (2 ^ OrderPreparation.width P) ^ 2 =
          2 ^ 2 * 2 ^ (OrderPreparation.width P * 2) := by
        rw [pow_mul]
        norm_num
      _ = 2 ^ (2 * OrderPreparation.width P + 2) := by
        rw [← pow_add]
        congr 1
        omega
  unfold Canonical.attemptFloor Canonical.successNumerator
  rw [Nat.cast_mul, denominator]

/-- The actual repeat count is exactly the reviewed closed logarithmic expression. -/
public lemma sampleCount_eq_closedForm (P : KnownOrderProblem G) :
    sampleCount P = Nat.ceil
      (Real.log ((1 : Real) / 3) /
        Real.log (1 - ((P.order : Real) * Nat.totient P.order) /
          2 ^ (2 * OrderPreparation.width P + 2))) := by
  rw [sampleCount_eq_signedLog, attemptFloor_eq_width]

/-- The same exact count drives the full-family two-thirds amplification. -/
private lemma twoThirds_le_success (P : KnownOrderProblem G) :
    ENNReal.ofReal ((2 : Real) / 3) ≤
      1 - (ENNReal.ofReal (Canonical.sourceFailureBudget P).value) ^ sampleCount P := by
  have threshold : FailureBudget.oneThird.successThreshold =
      ENNReal.ofReal ((2 : Real) / 3) := by
    norm_num [FailureBudget.successThreshold, FailureBudget.oneThird, FailureBudget.value]
  have bound := Canonical.successThreshold_le_one_sub_retryFailurePower P
    FailureBudget.oneThird FailureBudget.oneThird_wellFormed
  rw [threshold, ← sampleCount_eq_canonical] at bound
  exact bound

variable [Fintype G]

/-- The existing source Born proof already supplies the complete selected Fourier family. -/
public lemma selected_probability (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) (secret : Input P) :
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

/-- Independent samples at the stronger calibrated count contain a recoverable output
with probability at least two thirds. The actual reuse Born bridge supplies independence. -/
public lemma binaryDLP_selected_vector_probability (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) (secret : Input P) :
    ENNReal.ofReal ((2 : Real) / 3) ≤
      (PMF.independentReplicateVector (OrderBornBridge.outcomePMF P expansion)
        (sampleCount P)).toOuterMeasure
        {outcomes | ∃ index, Probability.SelectedOutcome P secret (outcomes.get index)} := by
  have amplified := PMF.independentReplicate_successProbability_ge
    (OrderBornBridge.outcomePMF P expansion)
    (Probability.SelectedOutcome P secret) (sampleCount P)
    (Probability.selectedOutcomeFamilyLowerBound P) (ENNReal.ofReal ((2 : Real) / 3))
    (selected_probability P expansion secret) (by
      rw [Canonical.one_sub_selectedRawOutcomeFamilyLowerBound_eq_sourceFailure]
      exact twoThirds_le_success P)
  rw [← PMF.independentReplicateVector_toList, PMF.toOuterMeasure_map_apply] at amplified
  have events :
      {outcomes : List.Vector
          (TerminalZMeasure.Outcome (OrderPreparation.width P + OrderPreparation.width P))
          (sampleCount P) |
        PMF.ContainsEvent (Probability.SelectedOutcome P secret) outcomes.toList} =
      {outcomes | ∃ index, Probability.SelectedOutcome P secret (outcomes.get index)} := by
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

end QuantumAlg.FiniteCyclicDLP.Binary
