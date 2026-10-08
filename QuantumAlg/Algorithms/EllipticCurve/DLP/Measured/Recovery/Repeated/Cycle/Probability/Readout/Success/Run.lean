/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Readout.Success.Concrete

/-!
# Named actual checked-section runs meet the relational success threshold

The code-equality interface is instantiated with the first and reused runs
that are used by the completed checked-section cycle. Both observations
refer to the real retained input/output distribution.
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

/-- The actual first completed checked section meets its independently
specified relational success lower bound on admitted inputs. -/
theorem firstCheckedSection_successLB_on_admittedInput
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register}
    (input : OracleInput .empty (sectionCtx E problem) Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState) :
    (checkedSectionSuccessLB E problem points seed).value ≤
      ((firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
        nontrivial (checkedSectionRead E problem)).relationalDistribution input).toOuterMeasure
        {pair | checkedSectionAccepts E problem pair.1 pair.2} := by
  generalize hrun : firstCheckedSectionRun E fieldTail sameWidth fits odd problem points
    seed nontrivial (checkedSectionRead E problem) = run
  have codeEq : run.code = firstCheckedSectionCode E fieldTail sameWidth fits odd
      problem points seed nontrivial := by rw [← hrun]; rfl
  have readout : run.output = Output.all _ (checkedSectionRead E problem) := by
    rw [← hrun]
    rfl
  exact firstCheckedSection_successLB_of_code E problem fieldTail sameWidth fits odd
    points seed nontrivial addends run codeEq readout input valid

/-- The actual reused checked section meets the same bound after predecessor
admission supplies the required quantum seed. -/
theorem reusedCheckedSection_successLB_on_admittedInput
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register}
    (input : OracleInput .empty (sectionCtx E problem) Reference)
    (valid : checkedSectionInputDomain E problem input.caller.localState)
    (seeded : checkedSectionSeededInitialization E fieldTail sameWidth fits problem seed
      input.localState) :
    (checkedSectionSuccessLB E problem points seed).value ≤
      ((reusedCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
        nontrivial (checkedSectionRead E problem)).relationalDistribution input).toOuterMeasure
        {pair | checkedSectionAccepts E problem pair.1 pair.2} := by
  generalize hrun : reusedCheckedSectionRun E fieldTail sameWidth fits odd problem points
    seed nontrivial (checkedSectionRead E problem) = run
  have codeEq : run.code = reusedCheckedSectionCode E fieldTail sameWidth fits odd
      problem points seed nontrivial := by rw [← hrun]; rfl
  have readout : run.output = Output.all _ (checkedSectionRead E problem) := by
    rw [← hrun]
    rfl
  exact reusedCheckedSection_successLB_of_code E problem fieldTail sameWidth fits odd
    points seed nontrivial addends run codeEq readout input valid seeded

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
