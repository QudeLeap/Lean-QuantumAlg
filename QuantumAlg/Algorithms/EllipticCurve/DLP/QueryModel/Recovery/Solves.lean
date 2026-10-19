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
public lemma ecdlpRecovery_whole_solves (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) :
    (wholeAlgorithm I expansion nontrivial count).Solves
      (wholeProblem I expansion nontrivial count) := by
  constructor
  · intro environment witness Reference original valid _initialized
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid.1
    have originalValid := valid.2
    exact ecdlpRecovery_run_success I A expansion nontrivial count original originalValid
  · intro environment witness Reference original valid _initialized requirement present
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid.1
    have same : requirement = wholeStateRequirement I := List.mem_singleton.mp present
    subst requirement
    exact AlgorithmRun.stateRequirement_of_reinitializedAt
      (run I expansion nontrivial count) (Sampling.sourceEnvironment I A) (wholeZeroSeed I)
      (ecdlpRecovery_code_reinitializedAt I A expansion nontrivial count)
      (.read (batchResultRead (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I))) original
  · intro environment witness Reference original valid _initialized
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid.1
    exact ecdlpRecovery_run_restoresBorrowed I A expansion nontrivial count original
  · intro environment witness _Reference _original valid _initialized path _supported
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid.1
    exact ecdlpRecovery_code_events_le I expansion nontrivial count path
  · intro environment witness _Reference _original valid _initialized path _supported
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid.1
    exact ecdlpRecovery_code_resident_le I expansion nontrivial count path
  · intro environment witness _Reference _original valid _initialized path _supported
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid.1
    exact ecdlpRecovery_code_auxiliary_le I expansion nontrivial count path
  · intro environment witness _Reference _original valid _initialized path _supported
    obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp
      valid.1
    exact Circuit.depth_le_weightedCount_of_pool_le (code I expansion nontrivial count)
      Resource.Event.quantumDuration
      (eventBudget I expansion nontrivial count) path
      (ecdlpRecovery_code_events_le I expansion nontrivial count path)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
