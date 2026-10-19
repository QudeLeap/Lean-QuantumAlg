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
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Execution.Circuit.Reassociation

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
public lemma ecdlpRecovery_round_solves (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    (roundAlgorithm I expansion nontrivial).Solves
      (roundProblem I expansion nontrivial) := by
  constructor
  · intro environment witness Reference original valid admitted
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid
    exact ecdlpRecovery_round_success I A expansion nontrivial original admitted
  · intro environment witness Reference original valid _admitted requirement present
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid
    have same : requirement = roundStateRequirement I := List.mem_singleton.mp present
    subst requirement
    exact ecdlpRecovery_round_stateRequirement I A expansion nontrivial original
  · intro environment witness Reference original valid _admitted
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact (ecdlpRecovery_round_restartCleanup I A expansion nontrivial).restores reference state
  · intro environment witness _Reference _original valid _admitted path _supported
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid
    exact ecdlpRecovery_round_events_le I expansion nontrivial path
  · intro environment witness _Reference _original valid _admitted path _supported
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid
    exact sampledAttempt_resident_le (Sampling.Reuse.code (allowAllocation := false) I expansion)
      (curve E) (modulus I nontrivial)
      (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I) path
  · intro environment witness _Reference _original valid _admitted path _supported
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid
    exact sampledAttempt_auxiliary_le (Sampling.Reuse.code (allowAllocation := false) I expansion)
      (curve E) (modulus I nontrivial)
      (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I) path
  · intro environment witness _Reference _original valid _admitted path _supported
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid
    exact Circuit.depth_le_weightedCount_of_pool_le (round I expansion nontrivial)
      Resource.Event.quantumDuration
      (roundEventBudget I expansion nontrivial) path
      (ecdlpRecovery_round_events_le I expansion nontrivial path)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
