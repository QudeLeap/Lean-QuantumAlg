/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit.Reassociation.Range
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Prefix.FullRun
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Terminal.Success

/-!
# Structural complete-cycle cuts of the actual generic ECC run

Each certificate uses only literal equalities of the selected instructions
and sequential associativity. Symbolic range induction exposes the same
physical resets at completed boundaries, retaining the exact initialization,
all attempts and final packing. These structural witnesses can transport a
fixed cycle schedule; final-channel equivalence alone cannot authorize cuts.
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

/-- The finite named attempts expose their original reset/readout/check bodies. -/
def persistentCheckedAttempts_reassociation (count : Nat) :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let readout := persistentSamplingReadout E fieldTail odd problem points
    let checked := persistentCheckedRecovery E problem nontrivial
    Circuit.Reassociation
      (persistentCheckedAttempts E fieldTail sameWidth fits odd problem points seed
        nontrivial count)
      (Circuit.forRange count fun _ => reset.seq (readout.seq checked)) := by
  dsimp only
  refine (Circuit.Reassociation.ofEq (persistentCheckedAttempts_forRange E fieldTail
    sameWidth fits odd problem points seed nontrivial count)).trans ?_
  exact Circuit.Reassociation.forRange count _ _ (fun _ =>
    (Circuit.Reassociation.ofEq (persistentCheckedAttempt_seq E fieldTail sameWidth fits
      odd problem points seed nontrivial)).trans (Circuit.Reassociation.seqAssoc _ _ _))

/-- For every count of at least two attempts the exact original run has the
initialized first cycle, unchanged reused/terminal suffix and actual final pack. -/
def exponentRepeatedRun_initializedFirstReassociation (count : Nat) :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let body := terminalCheckedSectionCode E fieldTail odd problem points nontrivial
    let suffix := Circuit.OperationalEquiv.rotatedTail reset body count
    let packed := packBatchResult
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)
    Circuit.Reassociation
      (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
        nontrivial ((count + 1) + 1)).code
      (((initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd problem points
        seed nontrivial).seq suffix).seq packed) := by
  dsimp only
  let initial := BitWord.selectForCircuit (exponentRepeatedInitial E problem)
  let allocation := retainPersistent
    (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)
  let first := firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
    nontrivial
  let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
  let body := terminalCheckedSectionCode E fieldTail odd problem points nontrivial
  let suffix := Circuit.OperationalEquiv.rotatedTail reset body count
  let packed := packBatchResult
    (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)
  have attempts := (persistentCheckedAttempts_reassociation E fieldTail sameWidth fits odd
    problem points seed nontrivial ((count + 1) + 1)).trans
      (Circuit.Reassociation.rotateRangeFirstCycle reset body count)
  have whole : Circuit.Reassociation
      (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
        nontrivial ((count + 1) + 1)).code
      (initial.seq ((allocation.seq (first.seq suffix)).seq packed)) :=
    .seq (.refl initial) (.seq (.seq (.refl allocation) attempts) (.refl packed))
  exact whole.trans
    ((Circuit.Reassociation.seqAssoc initial (allocation.seq (first.seq suffix))
      packed).symm.trans
      ((Circuit.Reassociation.seq (Circuit.Reassociation.seqAssoc initial allocation
        (first.seq suffix)).symm (.refl packed)).trans
        (.seq (Circuit.Reassociation.seqAssoc (initial.seq allocation) first suffix).symm
          (.refl packed))))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
