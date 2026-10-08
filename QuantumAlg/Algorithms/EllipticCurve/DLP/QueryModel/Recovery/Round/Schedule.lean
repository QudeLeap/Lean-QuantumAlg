/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Solves
public import QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Solves
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Admission
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round
import all QuantumAlg.Core.Execution.CycleSchedule.Identity
import all QuantumAlg.Core.Execution.CycleSchedule.Cleanup.Admission
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Circuit.Weighted

/-!
# Actual finite schedule of complete reused ECDLP rounds

Every requested round is an independently specified complete computation with
original success, native checked feedback, physical reset and real next-input
admission. The actual zero-length range tail is classical identity work.
Maximum complete-cycle depth bounds one whole sampling/checking/reset round;
the actual sequential depth and total events retain all requested rounds.
Initial allocation and the one final optional pack remain separate endpoint
obligations; this reused suffix does not certify the original whole run.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The named actual finite loop uses the original complete round at every prescribed index. -/
public def reusedRounds (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) :
    Circuit (Sampling.executionModel I A) (context I) (context I) :=
  Circuit.forRange count (fun _ => round I A expansion nontrivial)

/-- The caller requests exactly this many complete rounds, ending in classical identity work. -/
public def reusedRoundPlan (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) : (count : Nat) →
    (duration : Resource.Event (Sampling.executionModel I A) → Nat) →
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) →
    CyclePlan (Sampling.executionModel I A) (context I) (context I) .unit
  | 0, duration, unitQueries =>
      .classical (Circuit.identityProblem (model := Sampling.executionModel I A)
        (shape := .unit) (context I) duration (fun coordinate => nomatch coordinate) unitQueries)
  | count + 1, duration, unitQueries =>
      .seq (.cycle (roundProblem I A expansion nontrivial duration unitQueries))
        (reusedRoundPlan I A expansion nontrivial count duration unitQueries)

/-- The same actual range supplies protocol, physical cleanup and entry proofs at every cut. -/
public def reusedRoundSchedule (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) : (count : Nat) →
    (duration : Resource.Event (Sampling.executionModel I A) → Nat) →
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) →
    Circuit.CycleSchedule (reusedRoundPlan I A expansion nontrivial count duration unitQueries)
      (reusedRounds I A expansion nontrivial count)
  | 0, duration, unitQueries =>
      Circuit.identitySchedule (model := Sampling.executionModel I A) (context I)
        OutputRead.unit duration (fun coordinate => nomatch coordinate) unitQueries
  | count + 1, duration, unitQueries =>
      .seq (round I A expansion nontrivial) (reusedRounds I A expansion nontrivial count)
        (.complete _ (roundCompleteCycle I A expansion nontrivial duration unitQueries))
        (reusedRoundSchedule I A expansion nontrivial count duration unitQueries)
        (by
          intro Reference original admitted
          cases count with
          | zero => exact ⟨True.intro, True.intro⟩
          | succ count =>
              exact ⟨True.intro, ecdlpRecovery_round_nextInput_admitted I A expansion nontrivial
                original admitted.2⟩)
        (Or.inr ⟨ecdlpRecovery_round_restartCleanup I A expansion nontrivial⟩)

/-- Actual history projection preserves the predetermined seed after complete feedback. -/
public theorem ecdlpRecovery_round_nextInput_seeded (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) {Reference : Register}
    (original : OracleInput (Sampling.executionModel I A).classicalOracles (context I) Reference) :
    roundSeededDomain I A ((round I A expansion nontrivial).nextInput original).localState :=
  Circuit.ReinitializedAt.nextInput_jointSeeded (round I A expansion nontrivial) (roundZeroSeed I)
    (ecdlpRecovery_round_reinitializedAt I A expansion nontrivial) original

/-- Every certified reused-cycle path is bounded by one whole round's independent allowance. -/
public theorem ecdlpRecovery_reused_maximumCycleDepth_le (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (path : (reusedRounds I A expansion nontrivial count).Path) :
    (reusedRoundSchedule I A expansion nontrivial count duration unitQueries).maximumCycleDepth
      duration path ≤
        ResourcePool.weightedCount duration (roundEventBudget I A expansion nontrivial)
      := by
  induction count with
  | zero => exact Nat.zero_le _
  | succ count ih =>
      change max ((round I A expansion nontrivial).depth duration path.1)
        ((reusedRoundSchedule I A expansion nontrivial count duration unitQueries).maximumCycleDepth
          duration path.2) ≤ _
      exact max_le
        (Circuit.depth_le_weightedCount_of_pool_le (round I A expansion nontrivial) duration
          (roundEventBudget I A expansion nontrivial) path.1
          (ecdlpRecovery_round_events_le I A expansion nontrivial path.1)) (ih path.2)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
