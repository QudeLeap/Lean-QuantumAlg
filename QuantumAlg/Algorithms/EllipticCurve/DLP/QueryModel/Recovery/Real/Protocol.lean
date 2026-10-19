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

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Depth

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Calibration

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Calibration
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Probability.Model
import all QuantumAlg.Algorithms.Factoring.Common
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves

/-!
# Original public failure calibration on the complete declared ECDLP run

The original real target chooses the direct logarithmic repeat count.
Only the geometric success floor is strengthened; the actual code, full final
state, borrowed restoration, complete resources and cycle admission remain
the same. No caller-supplied prepared bank or extra success premise is added.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original real target strengthens only the geometric success floor of the same run. -/
public def realWholeProblem (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (η : Real) (positive : 0 < η) :
    Problem (Sampling.executionModel I) (Sampling.pre I) (post I)
      (.option (.unsignedWord (scalarWidth I))) :=
  { wholeProblem I expansion nontrivial (realRepetitionCount I η) with
    successLB := fun _ _ => ⟨ENNReal.ofReal (1 - η), ENNReal.ofReal_le_one.mpr
      (sub_le_self 1 positive.le)⟩ }

/-- The budget selects the direct logarithmic repeat count in the actual same code. -/
public def realWholeAlgorithm (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (η : Real) :
    Algorithm (Sampling.executionModel I) (Sampling.pre I) (post I)
      (.option (.unsignedWord (scalarWidth I))) :=
  wholeAlgorithm I expansion nontrivial (realRepetitionCount I η)

/-- All seven actual execution obligations retain the original public threshold. -/
public lemma realWholeAlgorithm_solves (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (η : Real) (positive : 0 < η) :
    (realWholeAlgorithm I expansion nontrivial η).Solves
      (realWholeProblem I expansion nontrivial η positive) := by
  have original := ecdlpRecovery_whole_solves I expansion nontrivial
    (realRepetitionCount I η)
  refine { original with success := ?_ }
  intro environment witness Reference input admitted _
  obtain ⟨A, rfl⟩ := (Sampling.admissible_iff_sourceEnvironment I environment).mp admitted.1
  exact ecdlpRecovery_run_real_success I A expansion nontrivial η positive
    input admitted.2

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
