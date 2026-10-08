/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Rotation
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cleanup.Support
import all QuantumAlg.Core.Execution.CycleSchedule.Cleanup.Sequence

/-!
# Physical cleanup of the real nonterminal ECC sections

Both the first and every reused nonterminal section end in the unchanged
physical reset of the following attempt. The terminal readout and check need
a separate output-state protocol; no reset is attributed to that final section.
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

omit [Fact p.Prime] in
private theorem persistentContext_noBorrowedQuantum :
    (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)).borrowedQuantumWires = [] :=
  (persistentCtx_borrowedQuantumWires _ _ _).trans
    (PublicInput.terminal_noBorrowedQuantum E (orderWidth problem))

/-- Every reused checked section followed by the next actual reset restores
the borrowed interface and every owned wire's fixed seed on full blocks. -/
theorem reusedCheckedSection_restartCleanup :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let body :=
      (persistentSamplingReadout E fieldTail odd problem points).seq
        (persistentCheckedRecovery E problem nontrivial)
    Circuit.RestartCleanup (body.seq reset) := by
  dsimp only
  let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
  let body := (persistentSamplingReadout E fieldTail odd problem points).seq
    (persistentCheckedRecovery E problem nontrivial)
  refine Circuit.RestartCleanup.after body reset ?_
    (persistentSamplingReset_restartCleanup E fieldTail sameWidth fits problem seed)
  intro Reference H _ state
  exact Circuit.borrowedRestored_of_noBorrowedQuantum body
    (persistentContext_noBorrowedQuantum E problem) Reference state

/-- Reused nonterminal sections reset to the original specified sampling
label after their checked readout, on every complete path. -/
theorem reusedCheckedSection_reinitializedAt :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let body :=
      (persistentSamplingReadout E fieldTail odd problem points).seq
        (persistentCheckedRecovery E problem nontrivial)
    Circuit.ReinitializedAt (body.seq reset)
      (persistentSamplingSeed E fieldTail sameWidth fits problem seed) := by
  dsimp only
  exact Circuit.RestartCleanup.afterAt _ _ _
    (persistentSamplingReset_reinitializedAt E fieldTail sameWidth fits problem seed)

/-- The first nonterminal checked section has the same complete physical
cleanup, including its own initial reset and the next attempt's reset. -/
theorem firstCheckedSection_restartCleanup :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let body :=
      (persistentSamplingReadout E fieldTail odd problem points).seq
        (persistentCheckedRecovery E problem nontrivial)
    Circuit.RestartCleanup ((reset.seq body).seq reset) := by
  dsimp only
  let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
  let body := (persistentSamplingReadout E fieldTail odd problem points).seq
    (persistentCheckedRecovery E problem nontrivial)
  refine Circuit.RestartCleanup.after (reset.seq body) reset ?_
    (persistentSamplingReset_restartCleanup E fieldTail sameWidth fits problem seed)
  intro Reference H _ state
  exact Circuit.borrowedRestored_of_noBorrowedQuantum (reset.seq body)
    (persistentContext_noBorrowedQuantum E problem) Reference state

/-- The first nonterminal section, including its initial sample reset and
following attempt reset, ends at the same predetermined physical label. -/
theorem firstCheckedSection_reinitializedAt :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let body :=
      (persistentSamplingReadout E fieldTail odd problem points).seq
        (persistentCheckedRecovery E problem nontrivial)
    Circuit.ReinitializedAt ((reset.seq body).seq reset)
      (persistentSamplingSeed E fieldTail sameWidth fits problem seed) := by
  dsimp only
  exact Circuit.RestartCleanup.afterAt _ _ _
    (persistentSamplingReset_reinitializedAt E fieldTail sameWidth fits problem seed)

/-- The first real nonterminal checked section retains its owned pure seed
after any finite grouping of complete physical execution records. -/
theorem firstCheckedSection_groupedPure :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let body :=
      (persistentSamplingReadout E fieldTail odd problem points).seq
        (persistentCheckedRecovery E problem nontrivial)
    Circuit.RestartCleanup.GroupedPure ((reset.seq body).seq reset) :=
  (firstCheckedSection_restartCleanup E fieldTail sameWidth fits odd problem
    points seed nontrivial).groupedPure

/-- The first checked section retains the predetermined reset label after
actual classical output grouping, including every hidden service and path. -/
theorem firstCheckedSection_groupedPureAt :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let body :=
      (persistentSamplingReadout E fieldTail odd problem points).seq
        (persistentCheckedRecovery E problem nontrivial)
    Circuit.RestartCleanup.GroupedPureAt ((reset.seq body).seq reset)
      (persistentSamplingSeed E fieldTail sameWidth fits problem seed) :=
  Circuit.RestartCleanup.groupedPureAt
    (firstCheckedSection_reinitializedAt E fieldTail sameWidth fits odd problem
      points seed nontrivial)

/-- Every reused nonterminal checked section has the same physical pure-state
law after complete classical records are grouped for the next attempt. -/
theorem reusedCheckedSection_groupedPure :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let body :=
      (persistentSamplingReadout E fieldTail odd problem points).seq
        (persistentCheckedRecovery E problem nontrivial)
    Circuit.RestartCleanup.GroupedPure (body.seq reset) :=
  (reusedCheckedSection_restartCleanup E fieldTail sameWidth fits odd problem
    points seed nontrivial).groupedPure

/-- Every reused checked section retains the same prescribed seed after a
finite classical read, with the original weighted density blocks intact. -/
theorem reusedCheckedSection_groupedPureAt :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let body :=
      (persistentSamplingReadout E fieldTail odd problem points).seq
        (persistentCheckedRecovery E problem nontrivial)
    Circuit.RestartCleanup.GroupedPureAt (body.seq reset)
      (persistentSamplingSeed E fieldTail sameWidth fits problem seed) :=
  Circuit.RestartCleanup.groupedPureAt
    (reusedCheckedSection_reinitializedAt E fieldTail sameWidth fits odd problem
      points seed nontrivial)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
