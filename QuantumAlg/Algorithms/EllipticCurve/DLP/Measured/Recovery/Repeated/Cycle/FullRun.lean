/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Rotation

/-!
# Boundary rotation on the named complete ECDLP run

The original exponent preparation is executed exactly once before the
persistent checked attempts. These certificates include that preparation,
the seven-cell allocation, the actual finite loop and final option pack.
Zero, one and at least two attempts are distinguished without enumerating
the generic repetition count.
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

/-- With zero attempts the actual run still performs preparation, persistent
allocation, the empty loop and final option packing. -/
theorem exponentRepeatedRun_zero_code :
    (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial 0).code =
      (BitWord.selectForCircuit (exponentRepeatedInitial E problem)).seq
        (((retainPersistent (model := .quantum AlgorithmGate.model .empty BitWord.model)
          (PublicInput.terminal E (orderWidth problem))
          (Canonical.Layout.fieldWidth E) (orderWidth problem)).seq
            (Circuit.id _)).seq
          (packBatchResult (model := .quantum AlgorithmGate.model .empty BitWord.model)
            (PublicInput.terminal E (orderWidth problem))
            (Canonical.Layout.fieldWidth E) (orderWidth problem))) := by
  rfl

/-- One attempt has an initial reset and a terminal checked readout, with no
nonterminal cycle boundary asserted. -/
def exponentRepeatedRun_one :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let body :=
      (persistentSamplingReadout E fieldTail odd problem points).seq
        (persistentCheckedRecovery E problem nontrivial)
    let setup := BitWord.selectForCircuit (exponentRepeatedInitial E problem)
    let allocation := retainPersistent
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)
    let terminal := packBatchResult
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)
    Circuit.OperationalEquiv
      (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
        nontrivial 1).code
      (setup.seq ((allocation.seq
        (reset.seq (Circuit.OperationalEquiv.rotatedTail reset body 0))).seq
          terminal)) := by
  dsimp only
  change Circuit.OperationalEquiv
    ((BitWord.selectForCircuit (exponentRepeatedInitial E problem)).seq
      (repeatedTailRun E fieldTail sameWidth fits odd problem points seed nontrivial 1).code)
    _
  rw [repeatedTailRun_checkedAttempts]
  exact Circuit.OperationalEquiv.prepend _
    ((Circuit.OperationalEquiv.prepend _
      (persistentCheckedAttempts_rotated E fieldTail sameWidth fits odd problem
        points seed nontrivial 0)).append _)

/-- For every symbolic count of at least two attempts, the complete named run
has the first physical `reset; readout; check; reset` section and the unchanged
remaining suffix, including all preparation and final packing. -/
def exponentRepeatedRun_firstCycle (count : Nat) :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let body :=
      (persistentSamplingReadout E fieldTail odd problem points).seq
        (persistentCheckedRecovery E problem nontrivial)
    let setup := BitWord.selectForCircuit (exponentRepeatedInitial E problem)
    let allocation := retainPersistent
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)
    let terminal := packBatchResult
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)
    Circuit.OperationalEquiv
      (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
        nontrivial ((count + 1) + 1)).code
      (setup.seq ((allocation.seq
        (((reset.seq body).seq reset).seq
          (Circuit.OperationalEquiv.rotatedTail reset body count))).seq
            terminal)) := by
  dsimp only
  change Circuit.OperationalEquiv
    ((BitWord.selectForCircuit (exponentRepeatedInitial E problem)).seq
      (repeatedTailRun E fieldTail sameWidth fits odd problem points seed nontrivial
        ((count + 1) + 1)).code)
    _
  exact Circuit.OperationalEquiv.prepend _
    (repeatedTailRun_firstCycle E fieldTail sameWidth fits odd problem points seed
      nontrivial count)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
