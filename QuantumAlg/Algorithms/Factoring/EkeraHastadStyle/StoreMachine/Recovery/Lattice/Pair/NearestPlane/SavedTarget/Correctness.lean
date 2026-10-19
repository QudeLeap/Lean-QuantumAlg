/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.NearestPlane.SavedTarget.Frames

/-!
# Actual nearest-plane result with original saved target and reduced basis

All final mathematical objects come from the original incoming sample pair:
the reduced basis, the three nearest-plane coefficients, the residual and the
independently copied original target. The complete caller read frame is retained.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairNearestPlaneSavedTarget

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- Copying the target preserves the original nearest-plane coefficients and residual. -/
lemma savedTargetInto_nearest (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (initial : InitialConditions store refs) :
    let samples := sourceSamples refs store
    let after := savedTargetStore refs store
    RawSignedRepresents (after.read (writeInput refs.pairNearest.first.division.output))
        (LatticeNearestPlaneShortLog.trace (shortLogBits N) (tradeoffBits N) samples).center.1 ∧
      RawSignedRepresents (after.read (writeInput refs.pairNearest.second.division.output))
        (LatticeNearestPlaneShortLog.trace (shortLogBits N) (tradeoffBits N) samples).center.2.1 ∧
      RawSignedRepresents (after.read (writeInput refs.pairNearest.third.division.output))
        (LatticeNearestPlaneShortLog.trace (shortLogBits N) (tradeoffBits N) samples).center.2.2 ∧
      LatticeArithmetic.PointRawRepresents after (nearestRefs refs).target
        (LatticeNearestPlaneShortLog.traceResidual (shortLogBits N) (tradeoffBits N) samples) :=
  LatticeNearestPlaneShortLog.threeInto_shortLog_correct N (shortLogBits N) (tradeoffBits N)
    (sourceSamples refs store) (nearestRefs refs) separation.nearest
    (copyStore refs (LatticeWideLllMachine.pairToLllStep refs.pairNearest.wide store).1)
    (nearest_initial_after_copy refs separation store initial)

/-- Original basis, center, residual, saved target and complete actual caller frame. -/
structure Outcome {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) (before after : Store ctx) : Prop where
  basis : LatticeMetricMachine.BasisRawRepresents after (nearestRefs refs).basis
    (LatticeNearestPlaneShortLog.basis (shortLogBits N) (tradeoffBits N)
      (sourceSamples refs before))
  first : RawSignedRepresents (after.read (writeInput refs.pairNearest.first.division.output))
    (LatticeNearestPlaneShortLog.trace (shortLogBits N) (tradeoffBits N)
      (sourceSamples refs before)).center.1
  second : RawSignedRepresents (after.read (writeInput refs.pairNearest.second.division.output))
    (LatticeNearestPlaneShortLog.trace (shortLogBits N) (tradeoffBits N)
      (sourceSamples refs before)).center.2.1
  third : RawSignedRepresents (after.read (writeInput refs.pairNearest.third.division.output))
    (LatticeNearestPlaneShortLog.trace (shortLogBits N) (tradeoffBits N)
      (sourceSamples refs before)).center.2.2
  residual : LatticeArithmetic.PointRawRepresents after (nearestRefs refs).target
    (LatticeNearestPlaneShortLog.traceResidual (shortLogBits N) (tradeoffBits N)
      (sourceSamples refs before))
  savedTarget : LatticeArithmetic.PointRawRepresents after refs.savedTarget
    (LatticeNearestPlaneShortLog.target (shortLogBits N) (tradeoffBits N)
      (sourceSamples refs before))
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

/-- The actual saved-target run returns the original mathematical objects and full caller frame. -/
lemma pairToNearestPlaneSavedTargetInto_correct (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (initial : InitialConditions store refs) :
    Outcome refs store (savedTargetStore refs store) := by
  have nearest := savedTargetInto_nearest refs separation store initial
  exact ⟨savedTargetInto_basis refs separation store initial,
    nearest.1, nearest.2.1, nearest.2.2.1, nearest.2.2.2,
    savedTargetInto_savedTarget refs separation store initial,
    pairToNearestPlaneSavedTargetInto_callerFrame refs store⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairNearestPlaneSavedTarget
