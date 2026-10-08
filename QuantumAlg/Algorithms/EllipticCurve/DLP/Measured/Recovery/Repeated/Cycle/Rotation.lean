/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Range
import all QuantumAlg.Core.Execution.Circuit.OperationalEquiv.Rotation

/-!
# Actual finite ECC attempt boundaries

For any symbolic number of attempts, the existing named run has the same
weighted execution when its unchanged reset boundaries are grouped at the end
of nonterminal sections. The tail certificate includes persistent allocation and packing;
completion and admission protocols are separate subsequent obligations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

/-- The actual checked attempts rotate into an initial reset, repeated
readout/recovery/reset sections, and a terminal readout/recovery section. -/
def persistentCheckedAttempts_rotated (count : Nat) :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let body :=
      (persistentSamplingReadout E fieldTail odd problem points).seq
        (persistentCheckedRecovery E problem nontrivial)
    Circuit.OperationalEquiv
      (persistentCheckedAttempts E fieldTail sameWidth fits odd problem points seed
        nontrivial (count + 1))
      (reset.seq (Circuit.OperationalEquiv.rotatedTail reset body count)) := by
  dsimp only
  exact (persistentCheckedAttempts_operationalEquiv E fieldTail sameWidth fits odd
    problem points seed nontrivial (count + 1)).trans
      (Circuit.OperationalEquiv.rotateRange _ _ count)

/-- For at least two attempts, the first nonterminal section visibly ends in
the physical reset of its successor. -/
def persistentCheckedAttempts_firstCycle (count : Nat) :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let body :=
      (persistentSamplingReadout E fieldTail odd problem points).seq
        (persistentCheckedRecovery E problem nontrivial)
    Circuit.OperationalEquiv
      (persistentCheckedAttempts E fieldTail sameWidth fits odd problem points seed
        nontrivial ((count + 1) + 1))
      (((reset.seq body).seq reset).seq
        (Circuit.OperationalEquiv.rotatedTail reset body count)) := by
  dsimp only
  exact (persistentCheckedAttempts_operationalEquiv E fieldTail sameWidth fits odd
    problem points seed nontrivial ((count + 1) + 1)).trans
      (Circuit.OperationalEquiv.rotateRangeFirstCycle _ _ count)

/-- The exact named returned run contains this first complete boundary,
including its unchanged one-time allocation and final pack. -/
def repeatedTailRun_firstCycle (count : Nat) :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let body :=
      (persistentSamplingReadout E fieldTail odd problem points).seq
        (persistentCheckedRecovery E problem nontrivial)
    let initial := retainPersistent (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)
    let terminal := packBatchResult
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)
    Circuit.OperationalEquiv
      (repeatedTailRun E fieldTail sameWidth fits odd problem points seed nontrivial
        ((count + 1) + 1)).code
      ((initial.seq (((reset.seq body).seq reset).seq
        (Circuit.OperationalEquiv.rotatedTail reset body count))).seq terminal) := by
  dsimp only
  rw [repeatedTailRun_checkedAttempts]
  exact (Circuit.OperationalEquiv.prepend _
    (persistentCheckedAttempts_firstCycle E fieldTail sameWidth fits odd problem
      points seed nontrivial count)).append _

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
