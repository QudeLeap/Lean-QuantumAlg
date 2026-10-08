/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.FullRun
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Prefix.Compatibility

/-!
# Initialized first cycle on the complete original ECC run

The existing exact boundary rotation is reassociated to put the original
initialization and allocation inside the first complete checked cycle. Full
weighted states, ordered events, dependency depth and live peaks are retained,
with no added operation or reset and no expansion of the symbolic retry count.
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

/-- Every source run with at least two symbolic attempts has the certified
initialized first code, the unchanged rotated suffix and the real final pack. -/
def exponentRepeatedRun_initializedFirstCycle (count : Nat) :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let body := (persistentSamplingReadout E fieldTail odd problem points).seq
      (persistentCheckedRecovery E problem nontrivial)
    let suffix := Circuit.OperationalEquiv.rotatedTail reset body count
    let packed := packBatchResult
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)
    Circuit.OperationalEquiv
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
  let body := (persistentSamplingReadout E fieldTail odd problem points).seq
    (persistentCheckedRecovery E problem nontrivial)
  let suffix := Circuit.OperationalEquiv.rotatedTail reset body count
  let packed := packBatchResult
    (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)
  exact (exponentRepeatedRun_firstCycle E fieldTail sameWidth fits odd problem points seed
    nontrivial count).trans
      ((Circuit.seqAssocOperationalEquiv initial (allocation.seq (first.seq suffix))
        packed).symm.trans
        (((Circuit.seqAssocOperationalEquiv initial allocation (first.seq suffix)).symm.append
          packed).trans
          ((Circuit.seqAssocOperationalEquiv (initial.seq allocation) first suffix).symm.append
            packed)))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
