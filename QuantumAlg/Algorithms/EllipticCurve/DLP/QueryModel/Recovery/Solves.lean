/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Success
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Zero
public import QuantumAlg.Core.Algorithm.AlgorithmRun.FixedOutput
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Weighted

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Protocol

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing

/-!
# The same original finite ECDLP run establishes its complete protocol
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The same actual finite run establishes all prescribed clauses, including zero rounds. -/
public theorem ecdlpRecovery_whole_solves (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    (wholeAlgorithm I A expansion nontrivial count).Solves
      (wholeProblem I A expansion nontrivial count duration unitQueries) := by
  constructor
  · intro Reference original valid _initialized
    exact ecdlpRecovery_run_success I A expansion nontrivial count original valid
  · intro Reference original _valid _initialized requirement present
    have same : requirement = wholeStateRequirement I := List.mem_singleton.mp present
    subst requirement
    exact AlgorithmRun.stateRequirement_of_reinitializedAt
      (run I A expansion nontrivial count) (wholeZeroSeed I)
      (ecdlpRecovery_code_reinitializedAt I A expansion nontrivial count)
      (.read (batchResultRead (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I))) original
  · intro Reference original _valid _initialized
    exact ecdlpRecovery_run_restoresBorrowed I A expansion nontrivial count original
  · intro _Reference _original _valid _initialized path _supported
    exact ecdlpRecovery_code_events_le I A expansion nontrivial count path
  · intro _Reference _original _valid _initialized path _supported
    exact ecdlpRecovery_code_resident_le I A expansion nontrivial count path
  · intro _Reference _original _valid _initialized path _supported
    exact ecdlpRecovery_code_auxiliary_le I A expansion nontrivial count path
  · intro _Reference _original _valid _initialized path _supported
    exact Circuit.depth_le_weightedCount_of_pool_le (code I A expansion nontrivial count) duration
      (eventBudget I A expansion nontrivial count) path
      (ecdlpRecovery_code_events_le I A expansion nontrivial count path)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
