/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Readout.Success

/-!
# Concrete first and reused checked-section success

The first and reused checked-section circuit identities feed their existing
retention and physical failure-contraction theorems to the relational success
bridge. The run remains an explicit parameter so the proof checks code and
readout interfaces without expanding an entire named run in its conclusion.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (problem : KnownOrderProblem E.GroupPoint)

private abbrev sectionCtx : RuntimeCtx .quantum :=
  persistentCtx (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)

/-- A run with the actual first reset/readout/check/reset code and declared
readout meets the independent checked-section relational success threshold. -/
theorem firstCheckedSection_successLB_of_code
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (run : AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))))
    (codeEq : run.code = firstCheckedSectionCode E fieldTail sameWidth fits odd
      problem points seed nontrivial)
    (readout : run.output = Output.all _ (checkedSectionRead E problem))
    {Reference : Register}
    (input : OracleInput .empty (sectionCtx E problem) Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState) :
    (checkedSectionSuccessLB E problem points seed).value ≤
      (run.relationalDistribution input).toOuterMeasure
        {pair | checkedSectionAccepts E problem pair.1 pair.2} := by
  have keepsValidity : RetainsValidity E problem run.code := by
    rw [codeEq]
    exact firstCheckedSection_retainsValidity E fieldTail sameWidth fits odd
      problem points seed nontrivial
  have keepsBound : RetainsSelectedBound E problem run.code := by
    rw [codeEq]
    exact firstCheckedSection_retainsSelectedBound E fieldTail sameWidth fits odd
      problem points seed nontrivial
  have keepsFirst : RetainsFirst E problem run.code := by
    rw [codeEq]
    exact firstCheckedSection_retainsFirst E fieldTail sameWidth fits odd
      problem points seed nontrivial (checkedSectionRead E problem)
  have contraction := firstCheckedSection_failureWeight_on_admittedInput E fieldTail
    sameWidth fits odd problem points seed nontrivial addends input valid
  rw [← codeEq] at contraction
  exact checkedSection_successLB_of_failureContract E problem points seed run
    readout keepsValidity keepsBound keepsFirst input valid contraction

/-- A run with the unchanged reused readout/check/reset code meets the same
threshold when the predecessor supplied the prescribed physical seed. -/
theorem reusedCheckedSection_successLB_of_code
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (run : AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))))
    (codeEq : run.code = reusedCheckedSectionCode E fieldTail sameWidth fits odd
      problem points seed nontrivial)
    (readout : run.output = Output.all _ (checkedSectionRead E problem))
    {Reference : Register}
    (input : OracleInput .empty (sectionCtx E problem) Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState)
    (seeded : checkedSectionSeededInitialization E fieldTail sameWidth fits problem seed
      input.localState) :
    (checkedSectionSuccessLB E problem points seed).value ≤
      (run.relationalDistribution input).toOuterMeasure
        {pair | checkedSectionAccepts E problem pair.1 pair.2} := by
  have keepsValidity : RetainsValidity E problem run.code := by
    rw [codeEq]
    exact reusedCheckedSection_retainsValidity E fieldTail sameWidth fits odd
      problem points seed nontrivial
  have keepsBound : RetainsSelectedBound E problem run.code := by
    rw [codeEq]
    exact reusedCheckedSection_retainsSelectedBound E fieldTail sameWidth fits odd
      problem points seed nontrivial
  have keepsFirst : RetainsFirst E problem run.code := by
    rw [codeEq]
    exact reusedCheckedSection_retainsFirst E fieldTail sameWidth fits odd
      problem points seed nontrivial (checkedSectionRead E problem)
  have contraction := reusedCheckedSection_failureWeight_on_admittedInput E fieldTail
    sameWidth fits odd problem points seed nontrivial addends input valid seeded
  rw [← codeEq] at contraction
  exact checkedSection_successLB_of_failureContract E problem points seed run
    readout keepsValidity keepsBound keepsFirst input valid contraction

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
