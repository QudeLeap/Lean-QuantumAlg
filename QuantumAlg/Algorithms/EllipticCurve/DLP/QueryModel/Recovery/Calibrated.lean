/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Solves
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Solves
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Protocol
import all QuantumAlg.Core.Execution.Circuit.Weighted

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Success

public import QuantumAlg.Algorithms.EllipticCurve.DLP.Probability.Model
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Probability.Model
import all QuantumAlg.Algorithms.Factoring.Common
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves

/-!
# Original public failure calibration on the complete declared ECDLP run

The original rational target chooses the original logarithmic repeat count.
Only the geometric success floor is strengthened; the actual code, full final
state, borrowed restoration, complete resources and cycle admission remain
the same. No caller-supplied prepared bank or extra success premise is added.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original rational target strengthens only the geometric success floor of the same run. -/
public def calibratedWholeProblem (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed) :
    Problem (Sampling.executionModel I) (Sampling.pre I) (post I)
      (.option (.unsignedWord (scalarWidth I))) :=
  { wholeProblem I expansion nontrivial (retryCountForBudget I budget) with
    successLB := fun _ _ => ⟨budget.successThreshold, ENNReal.ofReal_le_one.mpr
      (sub_le_self 1 (Factoring.FailureBudget.value_nonneg budget wellFormed))⟩ }

/-- The budget selects the original logarithmic repeat count in the actual same code. -/
public def calibratedWholeAlgorithm (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (budget : Factoring.FailureBudget) :
    Algorithm (Sampling.executionModel I) (Sampling.pre I) (post I)
      (.option (.unsignedWord (scalarWidth I))) :=
  wholeAlgorithm I expansion nontrivial (retryCountForBudget I budget)

/-- All seven actual execution obligations retain the original public threshold. -/
public lemma calibratedWholeAlgorithm_solves (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed) :
    (calibratedWholeAlgorithm I expansion nontrivial budget).Solves
      (calibratedWholeProblem I expansion nontrivial budget wellFormed) := by
  have original := ecdlpRecovery_whole_solves I expansion nontrivial
    (retryCountForBudget I budget)
  refine { original with success := ?_ }
  intro environment witness Reference input admitted _
  obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp admitted.1
  exact ecdlpRecovery_run_calibrated_success I A expansion nontrivial budget wellFormed
    input admitted.2

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
