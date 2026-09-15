/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Checked
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Reset
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Readout
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling

/-!
# Actual finite measured ECDLP with complete workspace reuse

Original arithmetic and terminal storage are allocated once. Each round
really resets and seeds all existing quantum wires, executes the original
sampling and Z readout, and immediately runs complete checked recovery on
those stored results. The original seven first-success destinations are
retained once; only the final optional result is packed after the loop.

The seed is fixed before execution. Neither the number of rounds nor an
intermediate result changes the set of resident quantum wires. Probability
amplification and resource bounds are separate proofs about this actual code.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP Canonical.Probability
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The actual round resets the original full basis before the unchanged sampling and readout. -/
def samplingRound (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E) :
    Circuit (PublicInput.terminal E (orderWidth problem))
      (PublicInput.terminal E (orderWidth problem)) :=
  (samplingReset E fieldTail (orderWidth problem) sameWidth fits seed).seq
    (samplingReadout E fieldTail odd problem points)

/-- Preparation, original gates and readout reuse the same complete terminal context. -/
theorem samplingRound_isLocal (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E) :
    (samplingRound E fieldTail sameWidth fits odd problem points seed).IsLocal :=
  ⟨samplingReset_isLocal E fieldTail (orderWidth problem) sameWidth fits seed,
    samplingReadout_isLocal E fieldTail odd problem points⟩

/-- Finite actual sampling and checked recovery retain one workspace and one final result. -/
def exponentRepeatedRun (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (nontrivial : 2 ≤ problem.order) (count : Nat) :
    AlgorithmRun (PublicInput.before E (orderWidth problem)) (checkedContext E problem)
      (.option (.unsignedWord (orderWidth problem))) :=
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  let tail := sampledRecoveryRun (samplingRound E fieldTail sameWidth fits odd problem points seed)
    (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed) count
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem))
  { code := ((PublicInput.initializeWork E (orderWidth problem)).seq
      (PublicInput.allocateTerminal E (orderWidth problem))).seq tail.code
    output := tail.output }

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
