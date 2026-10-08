/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.NearestPlane.Program

/-!
# Actual original-sample nearest-plane center and residual

The actual LLL output basis and preserved source target establish every nearest-
plane input condition. No incoming denominator or other scratch zero is needed.
The actual coefficients and residual match the original pure recovery trace.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairNearestPlaneMachine

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- The actual original LLL output establishes the complete source nearest-plane entry contract. -/
theorem nearest_initial (refs : Refs ctx N) (separation : Separation refs) (store : Store ctx)
    (initial : InitialConditions store refs) :
    LatticeNearestPlaneThree.Initial (nearestRefs refs)
      (LatticeWideLllMachine.pairToLllStep (model := model) refs.wide store).1
      (LatticeNearestPlaneShortLog.basis (shortLogBits N) (tradeoffBits N)
        (LatticeWideLllMachine.sourceSamples refs.wide store))
      (LatticeNearestPlaneShortLog.target (shortLogBits N) (tradeoffBits N)
        (LatticeWideLllMachine.sourceSamples refs.wide store)) := by
  have wide := LatticeWideLllTargetPreservation.pairToLllInto_correct_target
    (model := model) refs.wide
    separation.wide separation.target store initial
  have basisRaw := wide.invariant.basis
  rw [LatticeWideLllMachine.finalState_basis_eq_shortLogRecoveryTrace_output] at basisRaw
  exact ⟨basisRaw .first, basisRaw .second, basisRaw .third, wide.target⟩

/-- Actual source-to-nearest-plane execution yields the original three coefficients and residual. -/
theorem pairToNearestPlaneInto_represents (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (initial : InitialConditions store refs) :
    let samples := LatticeWideLllMachine.sourceSamples refs.wide store
    let after := pairToNearestPlaneStore (model := model) refs store
    RawSignedRepresents (after.read (writeInput refs.first.division.output))
        (LatticeNearestPlaneShortLog.trace (shortLogBits N) (tradeoffBits N) samples).center.1 ∧
      RawSignedRepresents (after.read (writeInput refs.second.division.output))
        (LatticeNearestPlaneShortLog.trace (shortLogBits N) (tradeoffBits N) samples).center.2.1 ∧
      RawSignedRepresents (after.read (writeInput refs.third.division.output))
        (LatticeNearestPlaneShortLog.trace (shortLogBits N) (tradeoffBits N) samples).center.2.2 ∧
      LatticeArithmetic.PointRawRepresents after (nearestRefs refs).target
        (LatticeNearestPlaneShortLog.traceResidual (shortLogBits N) (tradeoffBits N) samples) :=
  LatticeNearestPlaneShortLog.threeInto_shortLog_correct N (shortLogBits N) (tradeoffBits N)
    (LatticeWideLllMachine.sourceSamples refs.wide store) (nearestRefs refs) separation.nearest
    (LatticeWideLllMachine.pairToLllStep (model := model) refs.wide store).1
    (nearest_initial refs separation store initial)

/-- Original pure center and residual, with the complete actual whole-run caller frame. -/
structure Outcome (refs : Refs ctx N) (before after : Store ctx) : Prop where
  first : RawSignedRepresents (after.read (writeInput refs.first.division.output))
    (LatticeNearestPlaneShortLog.trace (shortLogBits N) (tradeoffBits N)
      (LatticeWideLllMachine.sourceSamples refs.wide before)).center.1
  second : RawSignedRepresents (after.read (writeInput refs.second.division.output))
    (LatticeNearestPlaneShortLog.trace (shortLogBits N) (tradeoffBits N)
      (LatticeWideLllMachine.sourceSamples refs.wide before)).center.2.1
  third : RawSignedRepresents (after.read (writeInput refs.third.division.output))
    (LatticeNearestPlaneShortLog.trace (shortLogBits N) (tradeoffBits N)
      (LatticeWideLllMachine.sourceSamples refs.wide before)).center.2.2
  residual : LatticeArithmetic.PointRawRepresents after (nearestRefs refs).target
    (LatticeNearestPlaneShortLog.traceResidual (shortLogBits N) (tradeoffBits N)
      (LatticeWideLllMachine.sourceSamples refs.wide before))
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerSeparated refs other → after.read other = before.read other

/-- The complete actual run meets the original pure center, residual and caller-frame contract. -/
theorem pairToNearestPlaneInto_correct (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (initial : InitialConditions store refs) :
    Outcome refs store (pairToNearestPlaneStore (model := model) refs store) := by
  have result := pairToNearestPlaneInto_represents refs separation store initial
  exact ⟨result.1, result.2.1, result.2.2.1, result.2.2.2,
    pairToNearestPlaneInto_callerFrame refs store⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairNearestPlaneMachine
