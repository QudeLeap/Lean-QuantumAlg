/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Framing
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Run

/-!
# Original measured exponent run followed by actual checked recovery

Both original public points are present before the quantum program starts.
The actual terminal exponent cells feed the original complete recovery,
elliptic-curve candidate verification and first-success selector. The final
optional-word result is retained and packed by the actual classical tail.
Every final live entry remains in the complete output manifest.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP Canonical.Probability
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The actual measured terminal context plus all retained recovery and result destinations. -/
def checkedContext (problem : KnownOrderProblem E.GroupPoint) : RuntimeCtx .quantum :=
  batchResultCtx (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)

/-- Execute the original quantum sample and its complete actual checked recovery once. -/
def exponentCheckedRun (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (nontrivial : 2 ≤ problem.order) :
    AlgorithmRun (PublicInput.before E (orderWidth problem)) (checkedContext E problem)
      (.option (.unsignedWord (orderWidth problem))) :=
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  let tail := recoveryTailRun (Canonical.Layout.curveSpec E)
    (recoveryModulusSpec problem nontrivial)
    (fun _ : Fin 1 => rawRecoveryInput problem measured)
    (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem))
  { code := (PublicInput.exponentRun E fieldTail odd problem points).code.seq tail.code
    output := tail.output }

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
