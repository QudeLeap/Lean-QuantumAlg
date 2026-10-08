/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Readout.Success
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Readout.Admission
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Validity
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Selection

/-!
# Relational success of the actual terminal checked ECC body

The final `S;C` body is a seeded completed attempt without the next
iteration's reset. Its original accepted/selected readout obeys the same
independent source-derived floor and first-success relation.
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

/-- The unchanged last readout and checked recovery, with no following reset. -/
def terminalCheckedSectionCode :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem) :=
  (persistentSamplingReadout E fieldTail odd problem points).seq
    (persistentCheckedRecovery E problem nontrivial)

/-- Observe the original two latches at the completed terminal body. -/
def terminalCheckedSectionRun :
    AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))) :=
  ⟨terminalCheckedSectionCode E fieldTail odd problem points nontrivial,
    Output.all _ (checkedSectionRead E problem)⟩

/-- Any run of the actual terminal body meets the checked relational floor
when the predecessor supplies the independently specified physical seed. -/
theorem terminalCheckedSection_successLB_of_code
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (run : AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))))
    (codeEq : run.code = terminalCheckedSectionCode E fieldTail odd problem points
      nontrivial)
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
    exact checkedSectionBody_retainsValidity E fieldTail odd problem points nontrivial
  have keepsBound : RetainsSelectedBound E problem run.code := by
    rw [codeEq]
    exact checkedSectionBody_retainsSelectedBound E fieldTail odd problem points nontrivial
  have keepsFirst : RetainsFirst E problem run.code := by
    rw [codeEq]
    exact checkedSectionBody_retainsFirst E fieldTail odd problem points nontrivial
  have contraction := persistentCheckedReadout_failureWeight_on_admittedInput E fieldTail
    sameWidth fits odd problem points seed nontrivial addends input valid seeded
  unfold CheckedReadoutFailureContracts at contraction
  change persistentFailureWeight
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (ctx := PublicInput.terminal E (orderWidth problem))
      (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      ((terminalCheckedSectionCode E fieldTail odd problem points nontrivial).execute
        Reference (State.skip input.state)) ≤
      (1 - ((problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) -
          4 * Real.sqrt (preparedExceptionalMass problem points seed))) *
        persistentFailureWeight
          (model := .quantum AlgorithmGate.model .empty BitWord.model)
          (ctx := PublicInput.terminal E (orderWidth problem))
          (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
          (State.skip input.state) at contraction
  rw [← codeEq] at contraction
  exact checkedSection_successLB_of_failureContract E problem points seed run
    readout keepsValidity keepsBound keepsFirst input valid contraction

/-- The named last `S;C` run meets that floor without an added physical reset. -/
theorem terminalCheckedSection_successLB_on_admittedInput
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register}
    (input : OracleInput .empty (sectionCtx E problem) Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState)
    (seeded : checkedSectionSeededInitialization E fieldTail sameWidth fits problem seed
      input.localState) :
    (checkedSectionSuccessLB E problem points seed).value ≤
      ((terminalCheckedSectionRun E fieldTail odd problem points nontrivial).relationalDistribution
        input).toOuterMeasure
        {pair | checkedSectionAccepts E problem pair.1 pair.2} := by
  generalize hrun : terminalCheckedSectionRun E fieldTail odd problem points nontrivial = run
  have codeEq : run.code = terminalCheckedSectionCode E fieldTail odd problem points
      nontrivial := by rw [← hrun]; rfl
  have readout : run.output = Output.all _ (checkedSectionRead E problem) := by
    rw [← hrun]
    rfl
  exact terminalCheckedSection_successLB_of_code E fieldTail sameWidth fits odd problem
    points seed nontrivial addends run codeEq readout input valid seeded

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
