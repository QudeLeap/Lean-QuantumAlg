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

private lemma first_success (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) {Reference : Register}
    (original : OracleInput (Sampling.executionModel I).classicalOracles
      (Sampling.pre I) Reference)
    (valid : inputDomain I original.caller.localState) :
    ENNReal.ofReal (Sampling.Reuse.successFloor I) ≤
      ((firstRoundAlgorithm I expansion nontrivial).relationalDistribution
        (Sampling.sourceEnvironment I A) original).toOuterMeasure
        {pair | roundAccepts I pair.2} := by
  have lower := ecdlpRecovery_round_success I A expansion nontrivial
    ((allocationCode I).nextInput (Sampling.sourceEnvironment I A) original)
    (ecdlpRecovery_allocation_nextInput_admitted I A nontrivial original valid)
  exact AlgorithmRun.relationalSuccess_after_prefix (environment := Sampling.sourceEnvironment I
    A) (allocationCode I)
    (roundAlgorithm I expansion nontrivial).run original
    {pair | roundAccepts I pair.2} {result | roundAccepts I result}
    (ENNReal.ofReal (Sampling.Reuse.successFloor I)) lower (fun _ accepted => accepted)

/-- The actual first complete cycle establishes every independently fixed protocol clause. -/
public lemma ecdlpRecovery_firstRound_solves (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    (firstRoundAlgorithm I expansion nontrivial).Solves
      (firstRoundProblem I expansion nontrivial) := by
  constructor
  · intro environment witness Reference original valid _initialized
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid.1
    have originalValid := valid.2
    exact first_success I A expansion nontrivial original originalValid
  · intro environment witness Reference original valid _initialized requirement present
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid.1
    have same : requirement = firstRoundStateRequirement I := List.mem_singleton.mp present
    subst requirement
    exact AlgorithmRun.stateRequirement_of_reinitializedAt
      (firstRoundAlgorithm I expansion nontrivial).run
      (Sampling.sourceEnvironment I A) (roundZeroSeed I) (ecdlpRecovery_firstRound_reinitializedAt
        I A expansion nontrivial)
      (roundResultRead I) original
  · intro environment witness Reference original valid _initialized
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid.1
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact (ecdlpRecovery_firstRound_restartCleanup I A expansion nontrivial).restores
      reference state
  · intro environment witness _Reference _original valid _initialized path _supported
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid.1
    exact ecdlpRecovery_firstRound_events_le I expansion nontrivial path
  · intro environment witness _Reference _original valid _initialized path _supported
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid.1
    exact ecdlpRecovery_firstRound_resident_le I expansion nontrivial path
  · intro environment witness _Reference _original valid _initialized path _supported
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid.1
    exact ecdlpRecovery_firstRound_auxiliary_le I expansion nontrivial path
  · intro environment witness _Reference _original valid _initialized path _supported
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid.1
    exact Circuit.depth_le_weightedCount_of_pool_le (firstRound I expansion nontrivial)
      Resource.Event.quantumDuration
      (firstRoundEventBudget I expansion nontrivial) path
      (ecdlpRecovery_firstRound_events_le I expansion nontrivial path)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
