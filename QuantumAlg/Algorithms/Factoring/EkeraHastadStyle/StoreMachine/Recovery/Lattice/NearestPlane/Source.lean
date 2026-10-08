/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Program.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Bounds

/-!
# Short-log bridge for actual three-stage nearest-plane reduction

The original short-log operand bounds discharge every numeric phase condition.
The actual final store represents the original coefficient center and residual;
all scratch cells may contain arbitrary initial values.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneShortLog

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

/-- The reduced short-log basis used by the actual nearest-plane circuit. -/
def basis (m ell : Nat) (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell) :
    NumberTheory.IntegerBasis3 :=
  (RSA.shortLogRecoveryTrace m ell samples).output

/-- The reduced short-log target used by the actual nearest-plane circuit. -/
def target (m ell : Nat) (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell) :
    NumberTheory.IntegerPoint3 :=
  RSA.shortLogLatticeTarget m ell samples

/-- The pure nearest-plane trace for the reduced short-log instance. -/
def trace (m ell : Nat) (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell) :
    NumberTheory.NearestPlaneTrace3 (basis m ell samples) (target m ell samples) :=
  NumberTheory.nearestPlaneTrace3 (basis m ell samples) (target m ell samples)

/-- The target after subtracting the trace center's full basis combination. -/
def traceResidual (m ell : Nat)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell) :
    NumberTheory.IntegerPoint3 :=
  (target m ell samples).sub ((basis m ell samples).linearCombination
    (trace m ell samples).center)

/-- The short-log width envelope discharges the actual three-stage arithmetic contract. -/
theorem shortLog_threeFits (N m ell : Nat)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell) :
    LatticeNearestPlaneThree.Fits (RSA.ShortLogWidths.coordinateWidth N m ell)
      (basis m ell samples) (target m ell samples) := by
  have fits := LatticeNearestPlaneFits.shortLogFits N m ell samples
  exact ⟨fits.third, fits.second, fits.first, fits.firstDenominatorNonzero⟩

/-- The three stored coefficients are the source trace center; the target is its exact residual. -/
theorem threeInto_shortLog_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (N m ell : Nat) (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (refs : LatticeNearestPlaneThree.Refs ctx (RSA.ShortLogWidths.coordinateWidth N m ell))
    (separation : LatticeNearestPlaneThree.Separation refs) (store : Store ctx)
    (initial : LatticeNearestPlaneThree.Initial refs store
      (basis m ell samples) (target m ell samples)) :
    let after := (LatticeNearestPlaneThree.threeStep refs store).1
    RawSignedRepresents (after.read (writeInput refs.first.division.output))
        (trace m ell samples).center.1 ∧
      RawSignedRepresents (after.read (writeInput refs.second.division.output))
        (trace m ell samples).center.2.1 ∧
      RawSignedRepresents (after.read (writeInput refs.third.division.output))
        (trace m ell samples).center.2.2 ∧
      LatticeArithmetic.PointRawRepresents after refs.target (traceResidual m ell samples) := by
  have result := LatticeNearestPlaneThree.threeInto_correct refs separation store
    (basis m ell samples) (target m ell samples) initial (shortLog_threeFits N m ell samples)
  simp only [trace, traceResidual, NumberTheory.nearestPlaneTrace3_center,
    NumberTheory.IntegerBasis3.nearestPlaneCoefficientCenter]
  exact ⟨result.2.2.1, result.2.1, result.1, result.2.2.2⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneShortLog
