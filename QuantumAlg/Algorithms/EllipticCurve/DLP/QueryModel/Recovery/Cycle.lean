/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Protocol
import all QuantumAlg.Core.Execution.Circuit.Weighted

/-!
# Original-input complete-cycle certificates for the same finite ECDLP run

Every admitted count uses the fixed actual plan. The zero computation includes
real initialization and final packing; every positive computation uses its full
first and reused checked rounds followed by the one actual classical pack.
The maximum-cycle allowance depends on one completed computation's parameters,
never on the number of retries. Whole-run chronological depth remains separate.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original complete outcome and fixed finite plan for every admitted count. -/
public def fullCycleProblem (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    CycleProblem (Sampling.executionModel I A) (Sampling.pre I) (post I)
      (.option (.unsignedWord (scalarWidth I))) where
  outcome := wholeProblem I A expansion nontrivial count duration unitQueries
  plan := finitePlan I A expansion nontrivial count duration unitQueries

/-- Every real original caller supplies admission to the same complete finite schedule. -/
public def fullCycleCertificate (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Algorithm.CycleSolves (wholeAlgorithm I A expansion nontrivial count)
      (fullCycleProblem I A expansion nontrivial count duration unitQueries) where
  correctness := ecdlpRecovery_whole_solves I A expansion nontrivial count duration unitQueries
  schedule := finiteSchedule I A expansion nontrivial count duration unitQueries
  entry := by
    intro Reference original admitted
    cases count with
    | zero => exact admitted
    | succ further => exact admitted

/-- One complete-cycle allowance, independent of the number of requested retry rounds. -/
public def completeCycleDepthLimit (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat) : Nat :=
  max (ResourcePool.weightedCount duration (firstRoundEventBudget I A expansion nontrivial))
    (ResourcePool.weightedCount duration (eventBudget I A expansion nontrivial 0))

/-- Every actual admitted count has the same maximum allowance for its completed cycles. -/
public theorem ecdlpRecovery_finite_maximumCycleDepth_le (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (path : (code I A expansion nontrivial count).Path) :
    (finiteSchedule I A expansion nontrivial count duration unitQueries).maximumCycleDepth
      duration path ≤ completeCycleDepthLimit I A expansion nontrivial duration := by
  cases count with
  | zero =>
      change (code I A expansion nontrivial 0).depth duration path ≤ _
      exact (Circuit.depth_le_weightedCount_of_pool_le (code I A expansion nontrivial 0)
        duration (eventBudget I A expansion nontrivial 0) path
        (ecdlpRecovery_code_events_le I A expansion nontrivial 0 path)).trans
          (Nat.le_max_right _ _)
  | succ further =>
      change Circuit.CycleSchedule.maximumCycleDepth
        (positiveSchedule I A expansion nontrivial further duration unitQueries) duration path ≤ _
      exact (ecdlpRecovery_positive_maximumCycleDepth_le I A expansion nontrivial further
        duration unitQueries path).trans (Nat.le_max_left _ _)


/-- The same maximum bound applies through the complete original-input certificate. -/
public theorem ecdlpRecovery_cycleCertificate_maximumCycleDepth_le
    (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (path : (wholeAlgorithm I A expansion nontrivial count).run.code.Path) :
    (fullCycleCertificate I A expansion nontrivial count duration unitQueries).maximumCycleDepth
      duration path ≤ completeCycleDepthLimit I A expansion nontrivial duration :=
  ecdlpRecovery_finite_maximumCycleDepth_le I A expansion nontrivial count duration unitQueries path

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
