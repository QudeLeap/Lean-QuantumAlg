/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Cycle
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Cycle
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Success
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
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
public def calibratedWholeProblem (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed) :
    Problem (Sampling.executionModel I A) (Sampling.pre I) (post I)
      (.option (.unsignedWord (scalarWidth I))) :=
  { wholeProblem I A expansion nontrivial (retryCountForBudget I budget)
      (fun _ => 1) (fun _ => rfl) with
    successLB := ⟨budget.successThreshold, ENNReal.ofReal_le_one.mpr
      (sub_le_self 1 (Factoring.FailureBudget.value_nonneg budget wellFormed))⟩ }

/-- The budget selects the original logarithmic repeat count in the actual same code. -/
public def calibratedWholeAlgorithm (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (budget : Factoring.FailureBudget) :
    Algorithm (Sampling.executionModel I A) (Sampling.pre I) (post I)
      (.option (.unsignedWord (scalarWidth I))) :=
  wholeAlgorithm I A expansion nontrivial (retryCountForBudget I budget)

/-- All seven actual execution obligations retain the original public threshold. -/
public theorem calibratedWholeAlgorithm_solves (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed) :
    (calibratedWholeAlgorithm I A expansion nontrivial budget).Solves
      (calibratedWholeProblem I A expansion nontrivial budget wellFormed) := by
  have original := ecdlpRecovery_whole_solves I A expansion nontrivial
    (retryCountForBudget I budget) (fun _ => 1) (fun _ => rfl)
  refine { original with success := ?_ }
  intro Reference input admitted _
  exact ecdlpRecovery_run_calibrated_success I A expansion nontrivial budget wellFormed
    input admitted

/-- The original public outcome is combined with its same complete finite plan. -/
public def calibratedCycleProblem (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed) :
    CycleProblem (Sampling.executionModel I A) (Sampling.pre I) (post I)
      (.option (.unsignedWord (scalarWidth I))) where
  outcome := calibratedWholeProblem I A expansion nontrivial budget wellFormed
  plan := finitePlan I A expansion nontrivial (retryCountForBudget I budget)
    (fun _ => 1) (fun _ => rfl)

/-- Strengthening the public success target preserves the actual cycle plan and entry domain. -/
public def calibratedCycleCertificate (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed) :
    Algorithm.CycleSolves (calibratedWholeAlgorithm I A expansion nontrivial budget)
      (calibratedCycleProblem I A expansion nontrivial budget wellFormed) where
  correctness := calibratedWholeAlgorithm_solves I A expansion nontrivial budget wellFormed
  schedule := finiteSchedule I A expansion nontrivial (retryCountForBudget I budget)
    (fun _ => 1) (fun _ => rfl)
  entry := (fullCycleCertificate I A expansion nontrivial (retryCountForBudget I budget)
    (fun _ => 1) (fun _ => rfl)).entry


end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
