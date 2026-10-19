/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.Frequency.Gram
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Ideal.FrequencyKernel

/-!
# Actual and ideal event matrices agree on every original good source pair

The complete actual legal family has the same frequency kernel as the
unchanged ideal group observable on the original good columns. This equality
retains all off-diagonal source entries and the complete residual Reference.
It is not a comparison between physical executions or a success floor.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ActualGoodEffectAgreement

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg.Execution (Store)
open _root_.QuantumAlg.QuantumFourierTransform.Semiclassical (Bits)
open _root_.QuantumAlg.FiniteCyclicDLP (KnownOrderProblem orderWidth)
open Recovery.Stage.PointCoordinates (ResidualReference)
open GenericPointAddition.InPlace.Semantics (radixUnit)
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

/-- Every pair of original good reset columns has the unchanged ideal event matrix entry. -/
lemma eventEffect_good_reset_matrix
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool) :
    (ActualSelectedEffect.eventEffect (environment := environment) (m := orderWidth problem) E
      points
      (radixUnit p fieldTail.succ odd)
      Reference original (fun final =>
        event (ActualFrequencyEvent.resultBits p.size (orderWidth problem) final) = true)).matrix
      (left, (Recovery.Initialization.resetArithmeticLabel E fieldTail seed, (0, refLeft)))
      (right, (Recovery.Initialization.resetArithmeticLabel E fieldTail seed, (0, refRight))) =
      (ECDLP.Measured.idealBranchEffect problem seed event
        (ResidualReference p.size (orderWidth problem) Reference)).matrix
        (SourceControls.sourceValues (orderWidth problem) left, refLeft)
        (SourceControls.sourceValues (orderWidth problem) right, refRight) := by
  refine (ActualFrequencyGram.eventEffect_reset_frequencyGram E problem points seed addends
    fieldTail odd Reference original left right refLeft refRight leftGood rightGood
    (fun bits => event bits = true)).trans ?_
  refine Eq.trans ?_ (IdealFrequencyKernel.idealBranchEffect_matrix_pairRows problem seed event
    (ResidualReference p.size (orderWidth problem) Reference) left right refLeft refRight).symm
  apply Finset.sum_congr rfl
  intro frequency _
  dsimp only [SourceControls.sourceValues]
  split_ifs <;> simp_all only [and_self, if_true, if_false, mul_zero, mul_one]

end OriginalSchedule

end

end ActualGoodEffectAgreement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
