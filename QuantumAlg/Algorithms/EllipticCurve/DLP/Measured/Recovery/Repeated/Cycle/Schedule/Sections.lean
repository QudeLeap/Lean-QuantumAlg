/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Solves.First
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Solves.Reused
import all QuantumAlg.Core.Execution.CycleSchedule

/-!
# Certified physical boundaries of checked ECC sections

Each independent section protocol has a complete-cycle certificate for its
actual code and structural readout. Finite composition separately requires
entry compatibility and the physical cleanup at every quantum boundary.
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

/-- The first real checked section is one independently specified complete cycle. -/
def firstCheckedSectionCompleteCycle
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Circuit.CompleteCycle
      (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial)
      (checkedSectionProblem E fieldTail sameWidth fits problem points seed nontrivial
        addends) where
  output := Output.all _ (checkedSectionRead E problem)
  certified := firstCheckedSection_solves E fieldTail sameWidth fits odd problem
    points seed nontrivial addends

/-- A reused section is complete only on the seed supplied by its predecessor. -/
def reusedCheckedSectionCompleteCycle
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Circuit.CompleteCycle
      (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial)
      (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points seed
        nontrivial addends) where
  output := Output.all _ (checkedSectionRead E problem)
  certified := reusedCheckedSection_solves E fieldTail sameWidth fits odd problem
    points seed nontrivial addends

/-- The first section realizes the caller's one-cycle plan on its actual code. -/
def firstCheckedSectionSchedule
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Circuit.CycleSchedule
      (.cycle (checkedSectionProblem E fieldTail sameWidth fits problem points seed
        nontrivial addends))
      (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial) :=
  .complete _ (firstCheckedSectionCompleteCycle E fieldTail sameWidth fits odd problem
    points seed nontrivial addends)

/-- A seeded reused section realizes the corresponding one-cycle plan. -/
def reusedCheckedSectionSchedule
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Circuit.CycleSchedule
      (.cycle (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points
        seed nontrivial addends))
      (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial) :=
  .complete _ (reusedCheckedSectionCompleteCycle E fieldTail sameWidth fits odd problem
    points seed nontrivial addends)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
