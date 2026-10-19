/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.LegalGram
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.Good.OutcomeWeights
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.Frequency.Event

/-!
# The complete actual event Gram has the original frequency kernel

Reindexing the complete legal outcomes retains every point-outcome word and
canonical frequency. The original good columns identify their common scalar,
and actual family completeness proves that its total point weight is one.
The resulting selected event kernel keeps both Fourier phases, the original
full-group equality and every residual Reference coordinate.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ActualFrequencyGram

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg.Execution (Store)
open _root_.QuantumAlg.QuantumFourierTransform.Semiclassical (Bits)
open _root_.QuantumAlg.FiniteCyclicDLP (KnownOrderProblem orderWidth)
open Recovery.Stage.PointCoordinates (ResidualReference)
open GenericPointAddition.InPlace.Semantics (radixUnit)
open Recovery.Conversion.FreeSourceFamily (LegalOutcome pathFourierCoefficient)
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}

section OriginalSchedule

variable (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (addends : (fun index => (points index).toGroupPoint) =
    ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
      problem.generator problem.target)
  (fieldTail : Nat) (odd : Odd p) (Reference : Register)
  (original : Store (Recovery.Layout.terminal p.size (orderWidth problem)))
  (left right : Bits (orderWidth problem) × Bits (orderWidth problem))
  (refLeft refRight : (ResidualReference p.size (orderWidth problem) Reference).Index)
  (leftGood : ExceptionalOffsetAveraging.Admissible (2 * orderWidth problem)
    (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem))
    (fun index => (points index).toGroupPoint) seed.toGroupPoint
    (SourceControls.sourceValues (orderWidth problem) left))
  (rightGood : ExceptionalOffsetAveraging.Admissible (2 * orderWidth problem)
    (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem))
    (fun index => (points index).toGroupPoint) seed.toGroupPoint
    (SourceControls.sourceValues (orderWidth problem) right))

include addends leftGood rightGood

set_option maxHeartbeats 800000 in
-- The full legal-label reindexing and both Fourier phases require this bounded local budget.
/-- Summing all actual point outcomes leaves precisely the canonical selected frequency Gram. -/
lemma eventEffect_reset_frequencyGram
    (event : (Fin (2 * orderWidth problem) → Bool) → Prop) :
    (ActualSelectedEffect.eventEffect (environment := environment) (m := orderWidth problem) E
      points
      (radixUnit p fieldTail.succ odd)
      Reference original
      (fun final => event (ActualFrequencyEvent.resultBits p.size
        (orderWidth problem) final))).matrix
      (left, (Recovery.Initialization.resetArithmeticLabel E fieldTail seed, (0, refLeft)))
      (right, (Recovery.Initialization.resetArithmeticLabel E fieldTail seed, (0, refRight))) =
      ∑ frequency : Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem),
        if event (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
            frequency) then
          (star (FullFrequencyOrthogonality.pairRows (orderWidth problem) frequency left) *
            FullFrequencyOrthogonality.pairRows (orderWidth problem) frequency right) *
          (if ECDLP.Measured.idealGroupOutput problem seed
                (SourceControls.sourceValues (orderWidth problem) left) =
              ECDLP.Measured.idealGroupOutput problem seed
                (SourceControls.sourceValues (orderWidth problem) right) ∧ refLeft = refRight
            then 1 else 0)
        else 0 := by
  let labels := ReadoutFrequencyLabels.pointAndFrequencyEquiv p.size (orderWidth problem) original
  let pointWeight : ℂ := star (ActualGoodOutcomeWeights.amplitude p.size (orderWidth problem)) *
    ActualGoodOutcomeWeights.amplitude p.size (orderWidth problem)
  let kernel : ℂ := if ECDLP.Measured.idealGroupOutput problem seed
      (SourceControls.sourceValues (orderWidth problem) left) =
    ECDLP.Measured.idealGroupOutput problem seed
      (SourceControls.sourceValues (orderWidth problem) right) ∧ refLeft = refRight then 1 else 0
  let factor := fun frequency : Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem) =>
    star (FullFrequencyOrthogonality.pairRows (orderWidth problem) frequency left) *
      FullFrequencyOrthogonality.pairRows (orderWidth problem) frequency right
  have normalized := ActualGoodOutcomeWeights.complete_point_weight
    (environment := environment) (m := orderWidth problem) E points
    (radixUnit p fieldTail.succ odd) Reference left seed refLeft leftGood
  change (∑ _outcomes : Fin (2 * orderWidth problem) → ActualOutcomeLabels.PointOutcome p.size,
    pointWeight) = 1 at normalized
  have coefficient (outcome : LegalOutcome p (orderWidth problem) original)
      (source : Bits (orderWidth problem) × Bits (orderWidth problem)) :
      pathFourierCoefficient p.size (orderWidth problem) outcome.2.val source =
        FullFrequencyOrthogonality.pairRows (orderWidth problem) (labels outcome).2 source := by
    rw [ActualFamilyCompleteness.pathFourierCoefficient_pairRows]
    change _ = FullFrequencyOrthogonality.pairRows (orderWidth problem)
      (ReadoutFrequencyLabels.pointAndFrequencyEquiv p.size (orderWidth problem)
        original outcome).2 source
    rw [ReadoutFrequencyLabels.pointAndFrequencyEquiv_frequency]
  calc
    _ = ∑ outcome : LegalOutcome p (orderWidth problem) original,
        if event (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
            (labels outcome).2) then
          factor (labels outcome).2 * (pointWeight * kernel)
        else 0 := by
      rw [ActualLegalGram.eventEffect_reset_gram E problem points seed addends fieldTail odd
        Reference original left right refLeft refRight leftGood rightGood]
      apply Finset.sum_congr rfl
      intro outcome _
      simp only [ActualFrequencyEvent.resultBits_legalRun, coefficient, labels, factor,
        pointWeight, kernel, ActualGoodOutcomeWeights.amplitude]
    _ = ∑ outcome : (Fin (2 * orderWidth problem) → ActualOutcomeLabels.PointOutcome p.size) ×
          (Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem)),
        if event (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
            outcome.2) then
          factor outcome.2 * (pointWeight * kernel)
        else 0 := labels.sum_comp (fun outcome =>
          if event (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
              outcome.2) then factor outcome.2 * (pointWeight * kernel) else 0)
    _ = ∑ frequency : Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem),
        if event (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
            frequency) then factor frequency * kernel else 0 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro frequency _
      by_cases selected : event (ExceptionalOffsetAveraging.pairedBigEndianSelected
        (orderWidth problem) frequency)
      · simp only [if_pos selected]
        calc
          _ = factor frequency * ((∑ _outcomes : Fin (2 * orderWidth problem) →
              ActualOutcomeLabels.PointOutcome p.size, pointWeight) * kernel) := by
            rw [Finset.sum_mul, Finset.mul_sum]
          _ = factor frequency * kernel := by rw [normalized, one_mul]
      · simp only [if_neg selected, Finset.sum_const_zero]
    _ = _ := rfl

end OriginalSchedule

end

end ActualFrequencyGram
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
