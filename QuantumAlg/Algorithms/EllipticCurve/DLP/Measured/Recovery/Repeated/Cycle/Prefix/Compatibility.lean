/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Prefix.Admission
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Compatibility
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Cleanup
import all QuantumAlg.Core.Execution.CycleSchedule.InputDistribution.Sequence

/-!
# Actual first ECC section including its caller prefix

The real initialization and allocation precede the first checked physical
section. Their composition supplies the same successor state as the exact
intermediate input projection, and its final reset still measures, restores
borrowed resources and seeds every owned output for the next section.
These admission and cleanup facts do not replace its independent complete
computation protocol or its remaining correctness and resource obligations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

attribute [local irreducible] Circuit.nextInput

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

private abbrev sectionCtx : RuntimeCtx .quantum :=
  persistentCtx (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)

/-- The original one-time prefix and first checked reset-bounded section. -/
def initializedFirstCheckedSectionCode :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.before E (orderWidth problem)) (sectionCtx E problem) :=
  (checkedRunPrefix E problem).seq
    (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed nontrivial)

/-- Every admitted original caller supplies the full classical domain to the
successor of the real first section, including one-time initialization. -/
theorem initializedFirstCheckedSection_nextInput_domain
    {Reference : Register}
    (input : OracleInput .empty (PublicInput.before E (orderWidth problem)) Reference)
    (valid : PublicInput.inputDomain E (orderWidth problem) problem input.caller.localState) :
    checkedSectionInputDomain E problem
      ((initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd problem points
        seed nontrivial).nextInput input).caller.localState := by
  rw [initializedFirstCheckedSectionCode, Circuit.nextInput_seq]
  exact firstCheckedSection_nextInput_domain E fieldTail sameWidth fits odd problem
    points seed nontrivial ((checkedRunPrefix E problem).nextInput input)
    (checkedRunPrefix_nextInput_domain E problem nontrivial input valid)

/-- The complete actual first section supplies the fixed physical quantum seed
to its successor, without a separate caller seed assumption. -/
theorem initializedFirstCheckedSection_nextInput_seeded
    {Reference : Register}
    (input : OracleInput .empty (PublicInput.before E (orderWidth problem)) Reference) :
    checkedSectionSeededInitialization E fieldTail sameWidth fits problem seed
      ((initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd problem points
        seed nontrivial).nextInput input).localState := by
  rw [initializedFirstCheckedSectionCode, Circuit.nextInput_seq]
  exact firstCheckedSection_nextInput_seeded E fieldTail sameWidth fits odd problem points
    seed nontrivial ((checkedRunPrefix E problem).nextInput input)

/-- The physical first-section cleanup survives its actual initialization and
allocation prefix, with every borrowed and reference observation retained. -/
theorem initializedFirstCheckedSection_restartCleanup :
    Circuit.RestartCleanup
      (initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd problem points
        seed nontrivial) := by
  exact Circuit.RestartCleanup.after (checkedRunPrefix E problem)
    (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed nontrivial)
    (fun Reference {_} _ state => Circuit.borrowedRestored_of_noBorrowedQuantum
      (checkedRunPrefix E problem) (PublicInput.before_noBorrowedQuantum E (orderWidth problem))
      Reference state)
    (firstCheckedSection_restartCleanup E fieldTail sameWidth fits odd problem points
      seed nontrivial)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
