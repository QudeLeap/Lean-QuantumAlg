/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Sequence
import all QuantumAlg.Core.Execution.Circuit.OperationalEquiv.Range

/-!
# Symbolic finite checked attempts on the actual ECDLP recovery run

The unchanged named repeated run uses exactly this body. Reassociating each
actual reset, sample and checked recovery retains the complete weighted
execution and resources for arbitrary repetition count.
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

/-- The literal finite-loop body in the named repeated recovery run. -/
def persistentCheckedAttempts (count : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) :=
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  let round := BitWord.selectForCircuit
    (samplingRound E fieldTail sameWidth fits odd problem points seed)
  sampledAttempts round
    (BitWord.selectForCircuit_isLocal _
      (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed)) count
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem))

/-- The source loop is the finite range of the exact checked attempts. -/
theorem persistentCheckedAttempts_forRange (count : Nat) :
    persistentCheckedAttempts E fieldTail sameWidth fits odd problem points seed
      nontrivial count =
        Circuit.forRange count fun _ =>
          persistentCheckedAttempt E fieldTail sameWidth fits odd problem points seed
            nontrivial := by
  rfl

/-- Every symbolic repetition count has a complete execution and resource
equivalence to the same attempts with each internal reset exposed. -/
def persistentCheckedAttempts_operationalEquiv (count : Nat) :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let readout := persistentSamplingReadout E fieldTail odd problem points
    let checked := persistentCheckedRecovery E problem nontrivial
    Circuit.OperationalEquiv
      (persistentCheckedAttempts E fieldTail sameWidth fits odd problem points seed
        nontrivial count)
      (Circuit.forRange count fun _ => reset.seq (readout.seq checked)) := by
  dsimp only
  rw [persistentCheckedAttempts_forRange]
  exact Circuit.OperationalEquiv.forRange count _ _
    (fun _ => persistentCheckedAttempt_operationalEquiv E fieldTail sameWidth fits odd
      problem points seed nontrivial)

/-- The same finite body occurs inside the named returned algorithm run,
between its one-time persistent allocation and final option pack. -/
theorem repeatedTailRun_checkedAttempts (count : Nat) :
    (repeatedTailRun E fieldTail sameWidth fits odd problem points seed nontrivial count).code =
      ((retainPersistent (model := .quantum AlgorithmGate.model .empty BitWord.model)
        (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)).seq
          (persistentCheckedAttempts E fieldTail sameWidth fits odd problem points seed
            nontrivial count)).seq
        (packBatchResult (model := .quantum AlgorithmGate.model .empty BitWord.model)
          (PublicInput.terminal E (orderWidth problem))
          (Canonical.Layout.fieldWidth E) (orderWidth problem)) := by
  rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
