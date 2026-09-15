/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Input.Program.Resources

/-!
# Original target preserved by actual initialized fixed-fuel LLL

After the actual target has been loaded, its three coordinate reads lie outside
the original initialized driver's write set. The complete actual run therefore
returns both the original mathematical LLL invariant and the same loaded target.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideLllTargetPreservation

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

/-- A target read lies outside the original initialized driver's complete actual write set. -/
abbrev TargetInputSeparated {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : LatticeWideLllMachine.Refs ctx N) {shape : CShape}
    (other : CInputRef ctx shape) : Prop :=
  LatticeFixedFuelMachine.CallerSeparated refs.initialization.driver other

/-- Original separation needed to retain all three loaded target coordinates through LLL. -/
structure TargetPreservationSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : LatticeWideLllMachine.Refs ctx N) : Prop where
  first : TargetInputSeparated refs (LatticeState.coordinateInput refs.target.target.point.first)
  second : TargetInputSeparated refs (LatticeState.coordinateInput refs.target.target.point.second)
  third : TargetInputSeparated refs (LatticeState.coordinateInput refs.target.target.point.third)

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The independent target determined by the original actual terminal samples. -/
def loadedTarget (refs : LatticeWideLllMachine.Refs ctx N) (store : Store ctx) :
    NumberTheory.IntegerPoint3 :=
  RSA.shortLogLatticeTarget (shortLogBits N) (tradeoffBits N)
    (LatticeWideLllMachine.sourceSamples refs store)

/-- The full actual initialized LLL driver retains a supplied target-coordinate read. -/
theorem pairToLllInto_targetFrame (refs : LatticeWideLllMachine.Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : TargetInputSeparated refs other) :
    (LatticeWideLllMachine.pairToLllStep refs store).1.read other =
      (LatticeWideLllMachine.decodeTargetStep refs store).1.read other :=
  LatticeFixedFuelMachine.initializedInto_callerFrame
    (RSA.shortLogRecoveryFuel (shortLogBits N) (tradeoffBits N)) refs.initialization.driver
    (LatticeWideLllMachine.decodeTargetStep refs store).1 other separate

/-- All three actually loaded target coordinates survive the original initialized LLL run. -/
theorem pairToLllInto_preserves_loadedTarget (refs : LatticeWideLllMachine.Refs ctx N)
    (separation : LatticeWideLllMachine.Separation refs)
    (targetSeparation : TargetPreservationSeparation refs) (store : Store ctx)
    (initial : LatticeWideLllMachine.InitialConditions store refs) :
    LatticeArithmetic.PointRawRepresents (LatticeWideLllMachine.pairToLllStep refs store).1
      refs.target.target.point (loadedTarget refs store) := by
  have loaded := LatticeWideLllMachine.decodeTargetInto_target refs separation store initial
  refine ⟨?_, ?_, ?_⟩
  · change RawSignedRepresents ((LatticeWideLllMachine.pairToLllStep refs store).1.read
      (LatticeState.coordinateInput refs.target.target.point.first)) _
    rw [pairToLllInto_targetFrame refs store _ targetSeparation.first]
    exact loaded.1
  · change RawSignedRepresents ((LatticeWideLllMachine.pairToLllStep refs store).1.read
      (LatticeState.coordinateInput refs.target.target.point.second)) _
    rw [pairToLllInto_targetFrame refs store _ targetSeparation.second]
    exact loaded.2.1
  · change RawSignedRepresents ((LatticeWideLllMachine.pairToLllStep refs store).1.read
      (LatticeState.coordinateInput refs.target.target.point.third)) _
    rw [pairToLllInto_targetFrame refs store _ targetSeparation.third]
    exact loaded.2.2

/-- The original LLL invariant, loaded target and complete caller frame of the actual run. -/
structure RunTargetOutcome (refs : LatticeWideLllMachine.Refs ctx N)
    (before after : Store ctx) : Prop where
  invariant : LatticeFixedFuelMachine.StoreInvariant refs.initialization.driver
    (LatticeWideLllMachine.sourceBasis refs before) after
    (LatticeWideLllMachine.finalState refs before)
  target : LatticeArithmetic.PointRawRepresents after refs.target.target.point
    (loadedTarget refs before)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    LatticeWideLllMachine.CallerSeparated refs other → after.read other = before.read other

/-- The actual source-to-LLL run returns its original invariant and source target together. -/
theorem pairToLllInto_correct_target (refs : LatticeWideLllMachine.Refs ctx N)
    (separation : LatticeWideLllMachine.Separation refs)
    (targetSeparation : TargetPreservationSeparation refs) (store : Store ctx)
    (initial : LatticeWideLllMachine.InitialConditions store refs) :
    RunTargetOutcome refs store (LatticeWideLllMachine.pairToLllStep refs store).1 :=
  ⟨LatticeWideLllMachine.pairToLllInto_correct refs separation store initial,
    pairToLllInto_preserves_loadedTarget refs separation targetSeparation store initial,
    LatticeWideLllMachine.pairToLllInto_callerFrame refs store⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideLllTargetPreservation
