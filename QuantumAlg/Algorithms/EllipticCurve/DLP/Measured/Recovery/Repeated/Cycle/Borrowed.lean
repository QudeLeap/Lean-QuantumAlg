/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Readout
import all QuantumAlg.Core.Algorithm.Borrowed

/-!
# Borrowed restoration at actual completed ECC section boundaries

The physical reset certificates apply to arbitrary histories and references.
The run-level law accounts for the original store recorded as mathematical
history by the real `AlgorithmRun` interpreter.
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

/-- Every original first checked-section run restores the entire borrowed
classical, quantum and external-reference observation. -/
theorem firstCheckedSection_problemBorrowed
    {Reference : Register}
    (input : OracleInput .empty
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference) :
    (firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
      nontrivial (checkedSectionRead E problem)).RestoresBorrowed input := by
  apply AlgorithmRun.restoresBorrowed_of_circuit
    (firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
      nontrivial (checkedSectionRead E problem)) ?_ input
  intro Reference H _ state
  exact (firstCheckedSection_restartCleanup E fieldTail sameWidth fits odd problem
    points seed nontrivial).restores Reference state

/-- The reused checked-section run has the same unconditional borrowed
restoration on every reference extension and supported history. -/
theorem reusedCheckedSection_problemBorrowed
    {Reference : Register}
    (input : OracleInput .empty
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference) :
    (reusedCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
      nontrivial (checkedSectionRead E problem)).RestoresBorrowed input := by
  apply AlgorithmRun.restoresBorrowed_of_circuit
    (reusedCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
      nontrivial (checkedSectionRead E problem)) ?_ input
  intro Reference H _ state
  exact (reusedCheckedSection_restartCleanup E fieldTail sameWidth fits odd problem
    points seed nontrivial).restores Reference state

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
