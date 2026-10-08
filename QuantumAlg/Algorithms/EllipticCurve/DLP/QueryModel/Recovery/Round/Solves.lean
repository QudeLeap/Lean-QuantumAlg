/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Success
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.State
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Success
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.State
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Admission
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Resources
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Execution.CycleSchedule

/-!
# The actual complete ECDLP round solves its independent protocol

Original relational success, physical zero result fibers, full borrowed
restoration and every native path's complete event, space and serial-depth
allowances belong to the same real sampling/checking/feedback circuit.
Its actual next input admits another independently specified complete round.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The actual paid complete round meets every independent one-round obligation. -/
public theorem ecdlpRecovery_round_solves (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    (roundAlgorithm I A expansion nontrivial).Solves
      (roundProblem I A expansion nontrivial duration unitQueries) := by
  constructor
  · intro Reference original _valid admitted
    exact ecdlpRecovery_round_success I A expansion nontrivial original admitted
  · intro Reference original _valid _admitted requirement present
    have same : requirement = roundStateRequirement I := List.mem_singleton.mp present
    subst requirement
    exact ecdlpRecovery_round_stateRequirement I A expansion nontrivial original
  · intro Reference original _valid _admitted
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact (ecdlpRecovery_round_restartCleanup I A expansion nontrivial).restores reference state
  · intro _Reference _original _valid _admitted path _supported
    exact ecdlpRecovery_round_events_le I A expansion nontrivial path
  · intro _Reference _original _valid _admitted path _supported
    exact sampledAttempt_resident_le (Sampling.Reuse.code I A expansion)
      (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) (curve E) (modulus I nontrivial)
      (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I) path
  · intro _Reference _original _valid _admitted path _supported
    exact sampledAttempt_auxiliary_le (Sampling.Reuse.code I A expansion)
      (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) (curve E) (modulus I nontrivial)
      (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I) path
  · intro _Reference _original _valid _admitted path _supported
    exact Circuit.depth_le_weightedCount_of_pool_le (round I A expansion nontrivial) duration
      (roundEventBudget I A expansion nontrivial) path
      (ecdlpRecovery_round_events_le I A expansion nontrivial path)

/-- The same complete circuit, manifest and result implement the fixed one-round protocol. -/
public def roundCompleteCycle (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Circuit.CompleteCycle (round I A expansion nontrivial)
      (roundProblem I A expansion nontrivial duration unitQueries) where
  output := Output.all (context I) (roundResultRead I)
  certified := ecdlpRecovery_round_solves I A expansion nontrivial duration unitQueries

/-- The actual complete first round admits the independently fixed next-round protocol. -/
public theorem ecdlpRecovery_round_entryCompatible (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Circuit.EntryCompatible
      (.cycle (roundProblem I A expansion nontrivial duration unitQueries))
      (.cycle (roundProblem I A expansion nontrivial duration unitQueries))
      (round I A expansion nontrivial) := by
  intro Reference original admitted
  exact ⟨True.intro, ecdlpRecovery_round_nextInput_admitted I A expansion nontrivial
    original admitted.2⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
