/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Protocol
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Admission
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First
public import QuantumAlg.Core.Algorithm.AlgorithmRun.FixedOutput
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Success
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Prefix
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Weighted

/-!
# Complete original-input first-cycle acceptance

The actual allocation prefix supplies the real round's input. Its exact
continuation output law transfers the independently prescribed original
success floor without IID or fresh-service assumptions. The same actual
first cycle proves conditioned zero output, complete borrowed restoration,
all events, both live-space peaks and weighted dependency depth.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private theorem first_success (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) {Reference : Register}
    (original : OracleInput (Sampling.executionModel I A).classicalOracles
      (Sampling.pre I) Reference)
    (valid : inputDomain I original.caller.localState) :
    ENNReal.ofReal (Sampling.Reuse.successFloor I) ≤
      ((firstRoundAlgorithm I A expansion nontrivial).relationalDistribution
        original).toOuterMeasure
        {pair | roundAccepts I pair.2} := by
  have lower := ecdlpRecovery_round_success I A expansion nontrivial
    ((allocationCode I A).nextInput original)
    (ecdlpRecovery_allocation_nextInput_admitted I A nontrivial original valid)
  exact AlgorithmRun.relationalSuccess_after_prefix (allocationCode I A)
    (roundAlgorithm I A expansion nontrivial).run original
    {pair | roundAccepts I pair.2} {result | roundAccepts I result}
    (ENNReal.ofReal (Sampling.Reuse.successFloor I)) lower (fun _ accepted => accepted)

/-- The actual first complete cycle establishes every independently fixed protocol clause. -/
public theorem ecdlpRecovery_firstRound_solves (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    (firstRoundAlgorithm I A expansion nontrivial).Solves
      (firstRoundProblem I A expansion nontrivial duration unitQueries) := by
  constructor
  · intro Reference original valid _initialized
    exact first_success I A expansion nontrivial original valid
  · intro Reference original _valid _initialized requirement present
    have same : requirement = firstRoundStateRequirement I := List.mem_singleton.mp present
    subst requirement
    exact AlgorithmRun.stateRequirement_of_reinitializedAt
      (firstRoundAlgorithm I A expansion nontrivial).run
      (roundZeroSeed I) (ecdlpRecovery_firstRound_reinitializedAt I A expansion nontrivial)
      (roundResultRead I) original
  · intro Reference original _valid _initialized
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact (ecdlpRecovery_firstRound_restartCleanup I A expansion nontrivial).restores
      reference state
  · intro _Reference _original _valid _initialized path _supported
    exact ecdlpRecovery_firstRound_events_le I A expansion nontrivial path
  · intro _Reference _original _valid _initialized path _supported
    exact ecdlpRecovery_firstRound_resident_le I A expansion nontrivial path
  · intro _Reference _original _valid _initialized path _supported
    exact ecdlpRecovery_firstRound_auxiliary_le I A expansion nontrivial path
  · intro _Reference _original _valid _initialized path _supported
    exact Circuit.depth_le_weightedCount_of_pool_le (firstRound I A expansion nontrivial) duration
      (firstRoundEventBudget I A expansion nontrivial) path
      (ecdlpRecovery_firstRound_events_le I A expansion nontrivial path)

/-- The same real first-cycle code and complete live manifest implement its fixed protocol. -/
public def firstRoundCompleteCycle (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Circuit.CompleteCycle (firstRound I A expansion nontrivial)
      (firstRoundProblem I A expansion nontrivial duration unitQueries) where
  output := Output.all (context I) (roundResultRead I)
  certified := ecdlpRecovery_firstRound_solves I A expansion nontrivial duration unitQueries

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
