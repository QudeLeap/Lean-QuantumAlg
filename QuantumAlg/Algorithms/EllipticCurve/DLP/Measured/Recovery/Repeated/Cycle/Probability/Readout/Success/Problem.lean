/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Readout.Success.Run

/-!
# The independent checked-section problems consume actual-run success

Each problem's declared relational acceptance predicate and lower bound are
the independent checked-section definitions used by the named actual runs.
The seeded reused problem additionally requires its physical input seed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (problem : KnownOrderProblem E.GroupPoint)

private abbrev sectionCtx : RuntimeCtx .quantum :=
  persistentCtx (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)

/-- The named first section satisfies its independent problem's actual
relational success clause on every admitted input and reference extension. -/
theorem firstCheckedSection_problemSuccess
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register}
    (input : OracleInput .empty (sectionCtx E problem) Reference)
    (valid : (checkedSectionProblem E fieldTail sameWidth fits problem points seed
      nontrivial addends).valid input.caller.localState) :
    (checkedSectionProblem E fieldTail sameWidth fits problem points seed
      nontrivial addends).successLB.value ≤
      ((firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
        nontrivial (checkedSectionRead E problem)).relationalDistribution input).toOuterMeasure
        {pair | (checkedSectionProblem E fieldTail sameWidth fits problem points seed
          nontrivial addends).accepts pair.1 pair.2} := by
  change (checkedSectionSuccessLB E problem points seed).value ≤
    ((firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
      nontrivial (checkedSectionRead E problem)).relationalDistribution input).toOuterMeasure
      {pair | checkedSectionAccepts E problem pair.1 pair.2}
  exact firstCheckedSection_successLB_on_admittedInput E problem fieldTail sameWidth
    fits odd points seed nontrivial addends input valid

/-- The named reused section satisfies the same problem success clause when
its independent initialization predicate supplies the previous reset seed. -/
theorem reusedCheckedSection_problemSuccess
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register}
    (input : OracleInput .empty (sectionCtx E problem) Reference)
    (valid : (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points seed
      nontrivial addends).valid input.caller.localState)
    (seeded : (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points seed
      nontrivial addends).initialization input.localState) :
    (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points seed
      nontrivial addends).successLB.value ≤
      ((reusedCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
        nontrivial (checkedSectionRead E problem)).relationalDistribution input).toOuterMeasure
        {pair | (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points seed
          nontrivial addends).accepts pair.1 pair.2} := by
  change (checkedSectionSuccessLB E problem points seed).value ≤
    ((reusedCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
      nontrivial (checkedSectionRead E problem)).relationalDistribution input).toOuterMeasure
      {pair | checkedSectionAccepts E problem pair.1 pair.2}
  exact reusedCheckedSection_successLB_on_admittedInput E problem fieldTail sameWidth
    fits odd points seed nontrivial addends input valid seeded

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
