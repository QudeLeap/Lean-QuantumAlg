/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Schedule.Pair
import all QuantumAlg.Core.Execution.CycleSchedule.Identity

/-!
# Arbitrarily many nonterminal checked ECC sections

The right-associated finite range retains one completed physical reset per
nonterminal section and a classical identity at zero. This plan does not
include the distinct final readout/check or the surrounding setup and pack.
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

private abbrev sectionCtx : RuntimeCtx .quantum :=
  persistentCtx (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)

/-- The independently requested number of reused nonterminal cycles. -/
def reusedCheckedSectionRangePlan
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) : (count : Nat) →
    CyclePlan (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem)))
  | 0 => .classical (Circuit.identityProblem
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (shape := .product .bit (.unsignedWord (orderWidth problem)))
      (sectionCtx E problem) (fun _ => 1) (fun _ => rfl) (fun _ => rfl))
  | count + 1 =>
      .seq (.cycle (reusedCheckedSectionProblem E fieldTail sameWidth fits problem
        points seed nontrivial addends))
        (reusedCheckedSectionRangePlan addends count)

/-- The actual right-associated range of reused nonterminal section codes. -/
def reusedCheckedSectionRangeCode (count : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem) :=
  Circuit.forRange count fun _ =>
    reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial

/-- The arbitrary finite reused range satisfies every stated physical cut. -/
def reusedCheckedSectionRangeSchedule
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) : (count : Nat) →
    Circuit.CycleSchedule
      (reusedCheckedSectionRangePlan E fieldTail sameWidth fits problem points seed
        nontrivial addends count)
      (reusedCheckedSectionRangeCode E fieldTail sameWidth fits odd problem points seed
        nontrivial count)
  | 0 => Circuit.identitySchedule
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (checkedSectionRead E problem)
      (fun _ => 1) (fun _ => rfl) (fun _ => rfl)
  | count + 1 =>
      .seq _ _
        (reusedCheckedSectionSchedule E fieldTail sameWidth fits odd problem points
          seed nontrivial addends)
        (reusedCheckedSectionRangeSchedule addends count)
        (by
          intro Reference original admitted
          cases count with
          | zero => exact ⟨True.intro, True.intro⟩
          | succ count =>
              exact reusedCheckedSection_entryCompatible E fieldTail sameWidth fits
                odd problem points seed nontrivial addends Reference original admitted)
        (Or.inr ⟨reusedCheckedSection_restartCleanup E fieldTail sameWidth fits odd
          problem points seed nontrivial⟩)

/-- One first section followed by any finite number of reused nonterminal cycles. -/
def firstAndReusedCheckedSectionSchedule
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) (count : Nat) :
    Circuit.CycleSchedule
      (.seq (.cycle (checkedSectionProblem E fieldTail sameWidth fits problem points
        seed nontrivial addends))
        (reusedCheckedSectionRangePlan E fieldTail sameWidth fits problem points seed
          nontrivial addends count))
      ((firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial).seq
        (reusedCheckedSectionRangeCode E fieldTail sameWidth fits odd problem points
          seed nontrivial count)) :=
  .seq _ _
    (firstCheckedSectionSchedule E fieldTail sameWidth fits odd problem points seed
      nontrivial addends)
    (reusedCheckedSectionRangeSchedule E fieldTail sameWidth fits odd problem points
      seed nontrivial addends count)
    (by
      intro Reference original admitted
      cases count with
      | zero => exact ⟨True.intro, True.intro⟩
      | succ count =>
          exact firstCheckedSection_entryCompatible E fieldTail sameWidth fits odd
            problem points seed nontrivial addends Reference original admitted)
    (Or.inr ⟨firstCheckedSection_restartCleanup E fieldTail sameWidth fits odd
      problem points seed nontrivial⟩)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
