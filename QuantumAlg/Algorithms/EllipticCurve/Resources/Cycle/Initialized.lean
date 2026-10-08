/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.Resources.Solves
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Schedule.Initialized

/-!
# Original generic ECC correctness with its full finite cycle schedule

The same named generic algorithm satisfies its original outcome and the
independent initialized finite cycle plan. All original caller inputs reach
the first cycle, every actual reset supplies the next admitted input, and the
terminal classical option pack is included. The symbolic count here describes
at least two attempts; zero and one require their own fixed plans.
-/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open Execution PrimeFieldShortWeierstrass FiniteCyclicDLP
open PrimeFieldShortWeierstrass.ECDLP.Measured

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
  (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
  (seed : AffinePoint E) (addends : AddendEncoding E I points)

/-- The original outcome and fixed complete-cycle plan for the same actual finite run. -/
def initializedCycleProblem (count : Nat) (failure : ℝ) : CycleProblem
    (.quantum AlgorithmGate.model .empty BitWord.model)
    (inputContext E I) (outputContext E I)
    (.option (.unsignedWord (orderWidth (ECDLP.Canonical.problem I)))) where
  outcome := problem E I ((count + 1) + 1) failure
  plan := initializedRepeatedPlan E fieldTail sameWidth fits (ECDLP.Canonical.problem I)
    points seed I.subgroupOrder_prime.two_le addends count

/-- Original calibrated success, state/restoration, native resources and the
full physically admissible finite schedule on one named generic algorithm. -/
def initializedCycleCertificate (count : Nat) (failure : ℝ)
    (calibrated : RepetitionCondition E I points seed ((count + 1) + 1) failure) :
    Algorithm.CycleSolves
      (algorithm E fieldTail sameWidth fits odd I points seed ((count + 1) + 1))
      (initializedCycleProblem E fieldTail sameWidth fits I points seed addends count
        failure) where
  correctness := algorithm_solves E fieldTail sameWidth fits odd I points seed addends
    ((count + 1) + 1) failure calibrated
  schedule := exponentRepeatedRun_initializedSchedule E fieldTail sameWidth fits odd
    (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le addends count
  entry := by
    intro Reference input admitted
    apply (initializedRepeatedPlan_admits E fieldTail sameWidth fits
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le addends count input).mpr
    exact admitted.1

end

end QuantumAlg.EllipticCurve.LogicalResources
