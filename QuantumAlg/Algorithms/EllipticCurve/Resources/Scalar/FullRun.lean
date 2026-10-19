/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Spec
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.Events
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.EventCoordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.Time
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Base.Depth.WeightedCost

/-!
# Scalar bounds of the complete actual streaming execution

Quantum time sums only the actual round paths. The independent unit-duration
allowance separately charges the full initial bank and final pack, including
zero retries. The old 607-event initializer is never used to pay for 818 actual
preparations. No positive retry-count premise is introduced.
-/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
open scoped BigOperators
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.ExecutionContract
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery

/-- Actual finite preparation/measurement costs are independent of an Algorithm or Path. -/
public def Scalar.streamingWholeRunEvents
    (physicalWidth coordinateWidth sampleWidth count : Nat) : Nat :=
  PublicInput.Allocation.Events.bankWidth physicalWidth +
    count * ((Events.roundBudget physicalWidth sampleWidth).card +
      Scalar.recoveryEvents coordinateWidth sampleWidth) + 1

/-- Zero attempts still pay for the complete new bank and the terminal option pack. -/
lemma streamingWholeRunEvents_width256_zero (coordinateWidth sampleWidth : Nat) :
    Scalar.streamingWholeRunEvents 256 coordinateWidth sampleWidth 0 = 819 := by
  simp only [Scalar.streamingWholeRunEvents, Nat.zero_mul, Nat.add_zero]
  decide

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (r : Nat) (coefficient : (ZMod p)ˣ) (nontrivial : 2 ≤ problem.order) (count : Nat)

omit [Fact p.Prime] in
private lemma roundBudget_card_le_scalar :
    (Events.roundBudget p.size (orderWidth problem)).card ≤
      Scalar.roundEvents p.size (orderWidth problem) := by
  have positive : 0 < orderWidth problem := by
    apply Nat.clog_pos (by norm_num : 1 < 2)
    unfold oversampledOrder fourierOversamplingFactor
    have ordered := problem.order_pos
    omega
  have balance := EventCoordinates.roundBudget_card_balance p.size (orderWidth problem)
  omega

/-- The whole actual quantum computation is bounded by its actual finite round pools. -/
lemma streaming_run_quantumTime_scalar
    (path : (run E fieldTail problem points seed r coefficient nontrivial count).code.Path) :
    (run E fieldTail problem points seed r coefficient nontrivial count).code.quantumTime path ≤
      Scalar.wholeRunEvents p.size (ECDLP.Canonical.Layout.fieldWidth E)
        (orderWidth problem) count := by
  let sampleCode := round E fieldTail problem points seed r coefficient
  let curve := ECDLP.Canonical.Layout.curveSpec E
  let modulus := FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial
  let sample := recoveryInput (orderWidth problem)
    (PaidPacking.callerInput (PublicInput.AllocatedFixed.placement E (orderWidth problem)))
  let base := PublicInput.contextBaseRef E (orderWidth problem)
  let target := PublicInput.contextTargetRef E (orderWidth problem)
  let attempt := sampledAttempt sampleCode curve modulus sample base target
  let chosen : Fin count → sampleCode.Path := fun index =>
    Time.sampledAttemptSamplePath sampleCode curve modulus sample base target
      (Circuit.forRangeComponentPath count (fun _ => attempt) path.2.1.2 index)
  have serial :
      (run E fieldTail problem points seed r coefficient nontrivial count).code.quantumTime path =
        ∑ index : Fin count, sampleCode.quantumTime (chosen index) := by
    rw [Time.streamingRecovery_run_quantumTime]
    apply Finset.sum_congr rfl
    intro index _
    exact (Time.streamingRecovery_round_quantumTime E fieldTail problem points seed r coefficient
      (chosen index)).symm
  have sampled :
      (∑ index : Fin count, sampleCode.quantumTime (chosen index)) ≤
        count * Scalar.roundEvents p.size (orderWidth problem) := by
    refine (Finset.sum_le_sum (g := fun _ : Fin count =>
      Scalar.roundEvents p.size (orderWidth problem)) ?_).trans_eq ?_
    · intro index _
      have pool := Events.round_budget E fieldTail problem points seed r coefficient (chosen index)
      have weighted := Circuit.depth_le_weightedCount_of_pool_le sampleCode (fun _ => 1)
        (BitWord.liftQuantumPool (Events.roundBudget p.size (orderWidth problem)))
        (chosen index) pool
      have card : ResourcePool.weightedCount (fun _ => 1)
          (BitWord.liftQuantumPool (Events.roundBudget p.size (orderWidth problem))) =
            (Events.roundBudget p.size (orderWidth problem)).card := by
        rw [EventCoordinates.unitWeight_card, BitWord.liftQuantumPool_card]
      exact ((Circuit.quantumTime_le_unitDepth sampleCode (chosen index)).trans
        (weighted.trans_eq card)).trans (roundBudget_card_le_scalar E problem)
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  have total := (serial.trans_le sampled).trans
    (Nat.mul_le_mul_left count (Nat.le_add_right
      (Scalar.roundEvents p.size (orderWidth problem))
      (Scalar.recoveryEvents (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem))))
  unfold Scalar.wholeRunEvents
  omega

/-- Unit-duration depth keeps actual allocation even when the attempt count is zero. -/
lemma streaming_run_unitDepth_scalar
    (path : (run E fieldTail problem points seed r coefficient nontrivial count).code.Path) :
    (run E fieldTail problem points seed r coefficient nontrivial count).code.depth
        (fun _ => 1) path ≤
      Scalar.streamingWholeRunEvents p.size (ECDLP.Canonical.Layout.fieldWidth E)
        (orderWidth problem) count :=
  (EventCoordinates.run_unitDepth_le E problem fieldTail points seed r coefficient nontrivial
    count path).trans (EventCoordinates.fullBudget_card_le E problem nontrivial count)

end

end QuantumAlg.EllipticCurve.LogicalResources
