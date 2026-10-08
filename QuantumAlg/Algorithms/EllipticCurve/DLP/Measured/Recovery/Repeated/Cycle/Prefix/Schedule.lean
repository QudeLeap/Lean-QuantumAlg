/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Prefix.Solves
import all QuantumAlg.Core.Execution.CycleSchedule

/-!
# The original-caller first complete ECC cycle

The one-time prefix belongs inside the first independently specified cycle.
Its actual computation, reset and resource bounds are consumed together by
the complete-cycle interface. Later cycles retain their separate seeded
protocols and actual predecessor admission obligations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

/-- One complete first cycle includes the actual original initialization and
seven-cell allocation, one checked sample, and the next physical reset. -/
def initializedFirstCheckedSectionCompleteCycle
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Circuit.CompleteCycle
      (initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd problem points
        seed nontrivial)
      (initializedFirstCheckedSectionProblem E fieldTail sameWidth fits problem points seed
        nontrivial addends) where
  output := Output.all _ (checkedSectionRead E problem)
  certified := initializedFirstCheckedSection_solves E fieldTail sameWidth fits odd problem
    points seed nontrivial addends

/-- The real initialized first cycle realizes its independently fixed
single-cycle protocol, including every initialization dependency. -/
def initializedFirstCheckedSectionSchedule
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Circuit.CycleSchedule
      (.cycle (initializedFirstCheckedSectionProblem E fieldTail sameWidth fits problem points
        seed nontrivial addends))
      (initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd problem points
        seed nontrivial) :=
  .complete _ (initializedFirstCheckedSectionCompleteCycle E fieldTail sameWidth fits odd
    problem points seed nontrivial addends)

/-- The certified first cycle counts its actual initialization, check and
physical resets within the same symbolic depth allowance. -/
theorem initializedFirstCheckedSection_maximumDepth_le
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (path : (initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd problem
      points seed nontrivial).Path) :
    (initializedFirstCheckedSectionSchedule E fieldTail sameWidth fits odd problem points seed
      nontrivial addends).maximumCycleDepth (fun _ => 1) path ≤
        ResourcePool.weightedCount (fun _ => 1)
          (initializedFirstCheckedSectionEventBudget E problem nontrivial) :=
  initializedFirstCheckedSection_depth_le E fieldTail sameWidth fits odd problem points seed
    nontrivial path

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
