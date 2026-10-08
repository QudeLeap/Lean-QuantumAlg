/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Schedule.Sections
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Compatibility
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Cleanup

/-!
# Adjacent real checked ECC cycle boundaries

The first and reused sections compose only when the actual first reset
supplies the successor's independent seed and caller domain. The same law
holds between two reused sections.
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

/-- The actual first and reused sections form two certified physical cycles. -/
def firstReusedCheckedSectionSchedule
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Circuit.CycleSchedule
      (.seq
        (.cycle (checkedSectionProblem E fieldTail sameWidth fits problem points seed
          nontrivial addends))
        (.cycle (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points
          seed nontrivial addends)))
      ((firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial).seq
        (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
          nontrivial)) :=
  .seq _ _
    (firstCheckedSectionSchedule E fieldTail sameWidth fits odd problem points seed
      nontrivial addends)
    (reusedCheckedSectionSchedule E fieldTail sameWidth fits odd problem points seed
      nontrivial addends)
    (firstCheckedSection_entryCompatible E fieldTail sameWidth fits odd problem points
      seed nontrivial addends)
    (Or.inr ⟨firstCheckedSection_restartCleanup E fieldTail sameWidth fits odd problem
      points seed nontrivial⟩)

/-- Two reused sections have the same certified successor boundary. -/
def reusedPairCheckedSectionSchedule
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Circuit.CycleSchedule
      (.seq
        (.cycle (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points
          seed nontrivial addends))
        (.cycle (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points
          seed nontrivial addends)))
      ((reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial).seq
        (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
          nontrivial)) :=
  .seq _ _
    (reusedCheckedSectionSchedule E fieldTail sameWidth fits odd problem points seed
      nontrivial addends)
    (reusedCheckedSectionSchedule E fieldTail sameWidth fits odd problem points seed
      nontrivial addends)
    (reusedCheckedSection_entryCompatible E fieldTail sameWidth fits odd problem points
      seed nontrivial addends)
    (Or.inr ⟨reusedCheckedSection_restartCleanup E fieldTail sameWidth fits odd problem
      points seed nontrivial⟩)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
