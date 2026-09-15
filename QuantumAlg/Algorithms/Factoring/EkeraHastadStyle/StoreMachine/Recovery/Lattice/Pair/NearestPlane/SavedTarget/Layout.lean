/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.NearestPlane.Program.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Row.Movement

/-!
# Original saved-target cells and actual cross-phase frames

The original three-word copy retains the source target before nearest-plane
reduction overwrites its original target cells. Copy and suffix frames preserve
the original reduced basis and the independently retained source target.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairNearestPlaneSavedTarget

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

/-- Pair-to-nearest-plane references plus caller-owned storage for the target
before nearest-plane reduction overwrites its residual workspace. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  /-- Nested references for the pair nearest stage. -/
  pairNearest : LatticePairNearestPlaneMachine.Refs ctx N
  /-- Nested references for the saved target stage. -/
  savedTarget : LatticeState.PointRefs ctx (LatticeWideLllMachine.Width N)

/-- The nearest-plane phase retains the pair machine's original mutable target. -/
def nearestRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : LatticeNearestPlaneThree.Refs ctx (LatticeWideLllMachine.Width N) :=
  LatticePairNearestPlaneMachine.nearestRefs refs.pairNearest

/-- One read that survives the literal three-word target copy. -/
structure PointCopyFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (savedTarget : LatticeState.PointRefs ctx width) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  first : savedTarget.first.key ∉ other.storageKeys
  second : savedTarget.second.key ∉ other.storageKeys
  third : savedTarget.third.key ∉ other.storageKeys

/-- The copy preserves all original basis and target inputs consumed by nearest plane. -/
structure NearestInputCopyFrames {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : Prop where
  basisFirst : PointCopyFrameAvoids refs.savedTarget
    (LatticeState.coordinateInput (nearestRefs refs).basis.first.first)
  basisSecond : PointCopyFrameAvoids refs.savedTarget
    (LatticeState.coordinateInput (nearestRefs refs).basis.first.second)
  basisThird : PointCopyFrameAvoids refs.savedTarget
    (LatticeState.coordinateInput (nearestRefs refs).basis.first.third)
  basisFourth : PointCopyFrameAvoids refs.savedTarget
    (LatticeState.coordinateInput (nearestRefs refs).basis.second.first)
  basisFifth : PointCopyFrameAvoids refs.savedTarget
    (LatticeState.coordinateInput (nearestRefs refs).basis.second.second)
  basisSixth : PointCopyFrameAvoids refs.savedTarget
    (LatticeState.coordinateInput (nearestRefs refs).basis.second.third)
  basisSeventh : PointCopyFrameAvoids refs.savedTarget
    (LatticeState.coordinateInput (nearestRefs refs).basis.third.first)
  basisEighth : PointCopyFrameAvoids refs.savedTarget
    (LatticeState.coordinateInput (nearestRefs refs).basis.third.second)
  basisNinth : PointCopyFrameAvoids refs.savedTarget
    (LatticeState.coordinateInput (nearestRefs refs).basis.third.third)
  targetFirst : PointCopyFrameAvoids refs.savedTarget
    (LatticeState.coordinateInput (nearestRefs refs).target.first)
  targetSecond : PointCopyFrameAvoids refs.savedTarget
    (LatticeState.coordinateInput (nearestRefs refs).target.second)
  targetThird : PointCopyFrameAvoids refs.savedTarget
    (LatticeState.coordinateInput (nearestRefs refs).target.third)

/-- The saved target has no overlap with a write of the succeeding nearest-plane
phase, so its three coordinates are framed by that phase. -/
structure SavedTargetNearestFrames {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : Prop where
  first : LatticeNearestPlaneThree.FrameAvoids (nearestRefs refs)
    (LatticeState.coordinateInput refs.savedTarget.first)
  second : LatticeNearestPlaneThree.FrameAvoids (nearestRefs refs)
    (LatticeState.coordinateInput refs.savedTarget.second)
  third : LatticeNearestPlaneThree.FrameAvoids (nearestRefs refs)
    (LatticeState.coordinateInput refs.savedTarget.third)

/-- The nearest-plane phase frames all three coordinates of one retained point. -/
structure PointNearestFrames {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) (point : LatticeState.PointRefs ctx (LatticeWideLllMachine.Width N)) :
    Prop where
  first : LatticeNearestPlaneThree.FrameAvoids (nearestRefs refs)
    (LatticeState.coordinateInput point.first)
  second : LatticeNearestPlaneThree.FrameAvoids (nearestRefs refs)
    (LatticeState.coordinateInput point.second)
  third : LatticeNearestPlaneThree.FrameAvoids (nearestRefs refs)
    (LatticeState.coordinateInput point.third)

/-- The nearest-plane phase leaves every row of the final reduced basis intact. -/
structure BasisNearestFrames {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : Prop where
  first : PointNearestFrames refs (nearestRefs refs).basis.first
  second : PointNearestFrames refs (nearestRefs refs).basis.second
  third : PointNearestFrames refs (nearestRefs refs).basis.third

/-- Local separation for wide reduction, target preservation, copying, and the
literal nearest-plane phase. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : Prop where
  wide : LatticeWideLllMachine.Separation refs.pairNearest.wide
  target : LatticeWideLllTargetPreservation.TargetPreservationSeparation refs.pairNearest.wide
  copy : LatticeRows.PointCopySeparation refs.pairNearest.wide.target.target.point refs.savedTarget
  nearest : LatticeNearestPlaneThree.Separation (nearestRefs refs)
  copyPreservesNearestInputs : NearestInputCopyFrames refs
  savedTargetAvoidsNearestWrites : SavedTargetNearestFrames refs
  basisAvoidsNearestWrites : BasisNearestFrames refs

/-- A caller read outside all writes of the wide, copy, and nearest-plane stages. -/
structure CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) {shape : CShape} (other : CInputRef ctx shape) : Prop where
  wide : LatticeWideLllMachine.CallerSeparated refs.pairNearest.wide other
  copy : PointCopyFrameAvoids refs.savedTarget other
  nearest : LatticeNearestPlaneThree.FrameAvoids (nearestRefs refs) other

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairNearestPlaneSavedTarget
