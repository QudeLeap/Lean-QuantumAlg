/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Prefix.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Prefix.Compatibility
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Readout.Success.Run
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Prefix

/-!
# Actual first-cycle success from the original caller

The original prefix establishes the complete checked-section domain. The
exact sequential output law then transfers its independently stated success
floor to the initialized first cycle, retaining arbitrary reference and
persistent-service correlations.
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

/-- The complete actual first cycle observes the live accepted and selected
latches after its original initialization, checked sample and physical reset. -/
def initializedFirstCheckedSectionRun : AlgorithmRun
    (.quantum AlgorithmGate.model .empty BitWord.model)
    (PublicInput.before E (orderWidth problem)) (sectionCtx E problem)
    (.product .bit (.unsignedWord (orderWidth problem))) where
  code := (checkedRunPrefix E problem).seq
    (firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
      nontrivial (checkedSectionRead E problem)).code
  output := (firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
    nontrivial (checkedSectionRead E problem)).output

private theorem checkedAccepts_implies_initialized
    (before : Store (sectionCtx E problem))
    (value : CShape.Value (.product .bit (.unsignedWord (orderWidth problem))))
    (accepted : checkedSectionAccepts E problem before value) :
    initializedFirstCheckedSectionAccepts E problem value := by
  cases value with
  | product flag word => exact ⟨accepted.1, accepted.2.1, accepted.2.2.1⟩

theorem initializedFirstCheckedSection_success_of_runs
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (entryCode : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.before E (orderWidth problem)) (sectionCtx E problem))
    (entryEq : entryCode = checkedRunPrefix E problem)
    (checkedRun : AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))))
    (codeEq : checkedRun.code = firstCheckedSectionCode E fieldTail sameWidth fits odd
      problem points seed nontrivial)
    (outputEq : checkedRun.output = Output.all _ (checkedSectionRead E problem))
    (run : AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.before E (orderWidth problem)) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))))
    (composite : run = { code := entryCode.seq checkedRun.code, output := checkedRun.output })
    {Reference : Register}
    (input : OracleInput .empty (PublicInput.before E (orderWidth problem)) Reference)
    (valid : PublicInput.inputDomain E (orderWidth problem) problem input.caller.localState) :
    (checkedSectionSuccessLB E problem points seed).value ≤
      (run.relationalDistribution input).toOuterMeasure
        (Prod.snd ⁻¹' {value | initializedFirstCheckedSectionAccepts E problem value}) := by
  have admitted : checkedSectionInputDomain E problem
      (entryCode.nextInput input).caller.localState := by
    rw [entryEq]
    exact checkedRunPrefix_nextInput_domain E problem nontrivial input valid
  have lower := firstCheckedSection_successLB_of_code E problem fieldTail sameWidth fits odd
    points seed nontrivial addends checkedRun codeEq outputEq (entryCode.nextInput input) admitted
  have inclusion :
      {pair | checkedSectionAccepts E problem pair.1 pair.2} ⊆
        Prod.snd ⁻¹' {value | initializedFirstCheckedSectionAccepts E problem value} := by
    intro pair accepted
    exact checkedAccepts_implies_initialized E problem pair.1 pair.2 accepted
  rw [composite]
  exact AlgorithmRun.relationalSuccess_after_prefix entryCode checkedRun input
    {pair | checkedSectionAccepts E problem pair.1 pair.2}
    {value | initializedFirstCheckedSectionAccepts E problem value}
    (checkedSectionSuccessLB E problem points seed).value lower inclusion

/-- The real initialized first cycle meets its independent original-caller
relational success clause, without adding a latch or quantum seed condition. -/
theorem initializedFirstCheckedSection_problemSuccess
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register}
    (input : OracleInput .empty (PublicInput.before E (orderWidth problem)) Reference)
    (valid : PublicInput.inputDomain E (orderWidth problem) problem input.caller.localState) :
    (initializedFirstCheckedSectionProblem E fieldTail sameWidth fits problem points
      seed nontrivial addends).successLB.value ≤
      ((initializedFirstCheckedSectionRun E fieldTail sameWidth fits odd problem points
        seed nontrivial).relationalDistribution input).toOuterMeasure
          {pair | (initializedFirstCheckedSectionProblem E fieldTail sameWidth fits problem
            points seed nontrivial addends).accepts pair.1 pair.2} := by
  generalize named : initializedFirstCheckedSectionRun E fieldTail sameWidth fits odd
    problem points seed nontrivial = run
  have composite : run =
      { code := (checkedRunPrefix E problem).seq
          (firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
            nontrivial (checkedSectionRead E problem)).code
        output := (firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
          nontrivial (checkedSectionRead E problem)).output } := by
    rw [← named]
    rfl
  exact initializedFirstCheckedSection_success_of_runs E fieldTail sameWidth fits odd
    problem points seed nontrivial addends (checkedRunPrefix E problem) rfl
    (firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed nontrivial
      (checkedSectionRead E problem)) rfl rfl run composite input valid

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
