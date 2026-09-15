/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Run
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Probability.Recovery.Execution
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Retained

/-!
# Original measured exponent run followed by actual raw recovery

The actual exponent preparation, measured point cascade, inverse QFT and
retained finite readouts feed the original complete classical raw recovery.
Its optional result occupies a genuine additional retained cell. The output
manifest includes every original live resource and that result. This stage
returns the raw candidate and reconstruction flag; the subsequent elliptic
curve candidate verification and retry are separate actual program stages.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP
open ScalarMultiplication.MeasuredPlacement.Allocation

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- Actual original measurement cells plus one retained original raw-recovery result. -/
def exponentRecoveryContext (p width : Nat) : RuntimeCtx .quantum :=
  let ctx := exponentMeasurementContext p width
  ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.retainedCtx ctx width
    ctx.canonicalFreshKey ctx.canonicalFreshKey_fresh

/-- The complete shaped result reads the actual final retained optional value. -/
def exponentRecoveryRead (p width : Nat) :
    CInputRef (exponentRecoveryContext p width)
      (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.OutputShape width) :=
  let ctx := exponentMeasurementContext p width
  ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.retainedRead ctx width
    ctx.canonicalFreshKey ctx.canonicalFreshKey_fresh

/-- The real original measured exponent circuit executes before complete native raw recovery. -/
def exponentRecoveryRun (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (nontrivial : 2 ≤ problem.order) :
    AlgorithmRun (before p.size (2 * orderWidth problem))
      (exponentRecoveryContext p (orderWidth problem))
      (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.OutputShape (orderWidth problem)) :=
  let ctx := exponentMeasurementContext p (orderWidth problem)
  { code := .seq (exponentRun E fieldTail odd problem points).code
      (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.retainedCircuit
        (recoveryModulusSpec problem nontrivial)
        (rawRecoveryInput problem (QubitReadouts.input
          (exponentMeasurementCells p (orderWidth problem))))
        ctx.canonicalFreshKey ctx.canonicalFreshKey_fresh)
    output := Output.all (exponentRecoveryContext p (orderWidth problem))
      (.read (exponentRecoveryRead p (orderWidth problem))) }

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
