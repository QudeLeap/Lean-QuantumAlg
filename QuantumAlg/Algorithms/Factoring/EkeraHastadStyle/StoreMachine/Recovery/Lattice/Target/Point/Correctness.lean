/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Point

/-!
# Correctness of actual two-coordinate centered target loading

The second actual call reads the original second source and modulus; its frame
preserves the first actual output. Only the unmodified third coordinate retains
an incoming-zero requirement. Both scratch words are initialized by their calls.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTargetPoint

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The structural avoidance package frames the complete actual centered-coordinate call. -/
lemma centered_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : LatticeTarget.Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : AvoidsTargetWrites other refs) :
    (LatticeTarget.centeredTargetStep refs store).1.read other = store.read other :=
  LatticeTarget.centeredTargetInto_callerFrame refs store other
    avoids.1 avoids.2.1 avoids.2.2.1 avoids.2.2.2

/-- Every actual read outside both original coordinate write sets retains its exact value. -/
lemma loadTargetPointInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (first : AvoidsTargetWrites other refs.first) (second : AvoidsTargetWrites other refs.second) :
    (targetPointStep refs store).1.read other = store.read other :=
  (centered_callerFrame refs.second _ other second).trans
    (centered_callerFrame refs.first store other first)

/-- The independent original centered point formed from the supplied actual input cells. -/
def sourcePoint (refs : Refs ctx width) (store : Store ctx) :
    NumberTheory.IntegerPoint3 :=
  (RSA.ShortLogTarget.centeredValue (store.read refs.first.a).toNat
      (store.read refs.first.modulus).toNat,
    RSA.ShortLogTarget.centeredValue (store.read refs.second.a).toNat
      (store.read refs.second.modulus).toNat, 0)

/-- Actual coordinate outputs represent the original source point with the preserved third zero. -/
lemma loadTargetPointInto_represents {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx)
    (thirdZero : RawSignedRepresents
      (store.read (LatticeState.coordinateInput refs.point.third)) 0) :
    LatticeArithmetic.PointRawRepresents (targetPointStep refs store).1 refs.point
      (sourcePoint refs store) := by
  have first := LatticeTarget.centeredTargetInto_output refs.first separation.first store
  have second := LatticeTarget.centeredTargetInto_output refs.second separation.second
    (LatticeTarget.centeredTargetStep refs.first store).1
  have secondSource := centered_callerFrame refs.first store refs.second.a
    separation.secondAAvoidsFirst
  have secondModulus := centered_callerFrame refs.first store refs.second.modulus
    separation.secondModulusAvoidsFirst
  rw [secondSource, secondModulus] at second
  refine ⟨?_, ?_, ?_⟩
  · change RawSignedRepresents ((targetPointStep refs store).1.read
      (LatticeTarget.writeInput refs.point.first)) _
    rw [← refs.firstOutput]
    change RawSignedRepresents ((LatticeTarget.centeredTargetStep refs.second
      (LatticeTarget.centeredTargetStep refs.first store).1).1.read
        (LatticeTarget.writeInput refs.first.output)) _
    rw [centered_callerFrame refs.second _ _ separation.firstOutputAvoidsSecond]
    exact first
  · change RawSignedRepresents ((targetPointStep refs store).1.read
      (LatticeTarget.writeInput refs.point.second)) _
    rw [← refs.secondOutput]
    exact second
  · change RawSignedRepresents ((targetPointStep refs store).1.read
      (LatticeState.coordinateInput refs.point.third)) 0
    rw [loadTargetPointInto_callerFrame refs store _ separation.thirdAvoidsFirst
      separation.thirdAvoidsSecond]
    exact thirdZero

/-- Exact original target-point output and complete actual caller frame. -/
structure TargetPointOutcome (refs : Refs ctx width) (before after : Store ctx) : Prop where
  point : LatticeArithmetic.PointRawRepresents after refs.point (sourcePoint refs before)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    AvoidsTargetWrites other refs.first → AvoidsTargetWrites other refs.second →
      after.read other = before.read other

/-- The actual two-coordinate call meets the original contract without initial scratch zeros. -/
lemma loadTargetPointInto_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx)
    (thirdZero : RawSignedRepresents
      (store.read (LatticeState.coordinateInput refs.point.third)) 0) :
    TargetPointOutcome refs store (targetPointStep refs store).1 :=
  ⟨loadTargetPointInto_represents refs separation store thirdZero,
    loadTargetPointInto_callerFrame refs store⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTargetPoint
