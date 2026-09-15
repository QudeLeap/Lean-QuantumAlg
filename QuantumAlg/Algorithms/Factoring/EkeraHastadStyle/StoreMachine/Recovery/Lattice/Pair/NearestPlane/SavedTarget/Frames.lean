/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.NearestPlane.SavedTarget

/-!
# Actual point frames across target copying and nearest-plane reduction

The original copy frame retains all nine reduced-basis coordinates and all
three live target coordinates. The original suffix frames retain both the
independent saved target and the reduced basis during residual computation.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairNearestPlaneSavedTarget

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Actual copying preserves a represented point whose reads avoid the saved destinations. -/
theorem point_after_copy (refs : Refs ctx N) (store : Store ctx)
    (point : LatticeState.PointRefs ctx (LatticeWideLllMachine.Width N))
    (value : NumberTheory.IntegerPoint3)
    (rep : LatticeArithmetic.PointRawRepresents store point value)
    (first : PointCopyFrameAvoids refs.savedTarget (LatticeState.coordinateInput point.first))
    (second : PointCopyFrameAvoids refs.savedTarget (LatticeState.coordinateInput point.second))
    (third : PointCopyFrameAvoids refs.savedTarget (LatticeState.coordinateInput point.third)) :
    LatticeArithmetic.PointRawRepresents (copyStore refs store) point value := by
  refine ⟨?_, ?_, ?_⟩
  · change RawSignedRepresents ((copyStore refs store).read
      (LatticeState.coordinateInput point.first)) _
    rw [copy_callerFrame refs store _ first]
    exact rep.1
  · change RawSignedRepresents ((copyStore refs store).read
      (LatticeState.coordinateInput point.second)) _
    rw [copy_callerFrame refs store _ second]
    exact rep.2.1
  · change RawSignedRepresents ((copyStore refs store).read
      (LatticeState.coordinateInput point.third)) _
    rw [copy_callerFrame refs store _ third]
    exact rep.2.2

/-- Actual target copying retains every mathematical input needed by the original nearest plane. -/
theorem nearest_initial_after_copy (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (initial : InitialConditions store refs) :
    LatticeNearestPlaneThree.Initial (nearestRefs refs)
      (copyStore refs (LatticeWideLllMachine.pairToLllStep refs.pairNearest.wide store).1)
      (LatticeNearestPlaneShortLog.basis (shortLogBits N) (tradeoffBits N)
        (sourceSamples refs store))
      (LatticeNearestPlaneShortLog.target (shortLogBits N) (tradeoffBits N)
        (sourceSamples refs store)) := by
  have beforeCopy := LatticePairNearestPlaneMachine.nearest_initial refs.pairNearest
    ⟨separation.wide, separation.target, separation.nearest⟩ store initial
  let frames := separation.copyPreservesNearestInputs
  exact ⟨point_after_copy refs _ _ _ beforeCopy.first
      frames.basisFirst frames.basisSecond frames.basisThird,
    point_after_copy refs _ _ _ beforeCopy.second
      frames.basisFourth frames.basisFifth frames.basisSixth,
    point_after_copy refs _ _ _ beforeCopy.third
      frames.basisSeventh frames.basisEighth frames.basisNinth,
    point_after_copy refs _ _ _ beforeCopy.target
      frames.targetFirst frames.targetSecond frames.targetThird⟩

/-- Actual nearest-plane execution preserves any point with the supplied three read frames. -/
theorem point_after_nearest (refs : Refs ctx N) (store : Store ctx)
    (point : LatticeState.PointRefs ctx (LatticeWideLllMachine.Width N))
    (value : NumberTheory.IntegerPoint3)
    (rep : LatticeArithmetic.PointRawRepresents store point value)
    (first : LatticeNearestPlaneThree.FrameAvoids (nearestRefs refs)
      (LatticeState.coordinateInput point.first))
    (second : LatticeNearestPlaneThree.FrameAvoids (nearestRefs refs)
      (LatticeState.coordinateInput point.second))
    (third : LatticeNearestPlaneThree.FrameAvoids (nearestRefs refs)
      (LatticeState.coordinateInput point.third)) :
    LatticeArithmetic.PointRawRepresents
      (LatticeNearestPlaneThree.threeStep (nearestRefs refs) store).1 point value := by
  refine ⟨?_, ?_, ?_⟩
  · change RawSignedRepresents ((LatticeNearestPlaneThree.threeStep (nearestRefs refs) store).1.read
      (LatticeState.coordinateInput point.first)) _
    rw [LatticeNearestPlaneThree.threeInto_callerFrame (nearestRefs refs) store _ first]
    exact rep.1
  · change RawSignedRepresents ((LatticeNearestPlaneThree.threeStep (nearestRefs refs) store).1.read
      (LatticeState.coordinateInput point.second)) _
    rw [LatticeNearestPlaneThree.threeInto_callerFrame (nearestRefs refs) store _ second]
    exact rep.2.1
  · change RawSignedRepresents ((LatticeNearestPlaneThree.threeStep (nearestRefs refs) store).1.read
      (LatticeState.coordinateInput point.third)) _
    rw [LatticeNearestPlaneThree.threeInto_callerFrame (nearestRefs refs) store _ third]
    exact rep.2.2

/-- The original reduced source basis survives copying and every actual nearest-plane stage. -/
theorem savedTargetInto_basis (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (initial : InitialConditions store refs) :
    LatticeMetricMachine.BasisRawRepresents (savedTargetStep refs store).1 (nearestRefs refs).basis
      (LatticeNearestPlaneShortLog.basis (shortLogBits N) (tradeoffBits N)
        (sourceSamples refs store)) := by
  have copied := nearest_initial_after_copy refs separation store initial
  intro row
  cases row with
  | first =>
    exact point_after_nearest refs _ _ _ copied.first
      separation.basisAvoidsNearestWrites.first.first
      separation.basisAvoidsNearestWrites.first.second
      separation.basisAvoidsNearestWrites.first.third
  | second =>
    exact point_after_nearest refs _ _ _ copied.second
      separation.basisAvoidsNearestWrites.second.first
      separation.basisAvoidsNearestWrites.second.second
      separation.basisAvoidsNearestWrites.second.third
  | third =>
    exact point_after_nearest refs _ _ _ copied.third
      separation.basisAvoidsNearestWrites.third.first
      separation.basisAvoidsNearestWrites.third.second
      separation.basisAvoidsNearestWrites.third.third

/-- The copied target remains the original source target after all nearest-plane reductions. -/
theorem savedTargetInto_savedTarget (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (initial : InitialConditions store refs) :
    LatticeArithmetic.PointRawRepresents (savedTargetStep refs store).1 refs.savedTarget
      (LatticeNearestPlaneShortLog.target (shortLogBits N) (tradeoffBits N)
        (sourceSamples refs store)) := by
  have wide := LatticeWideLllTargetPreservation.pairToLllInto_correct_target refs.pairNearest.wide
    separation.wide separation.target store initial
  have copied := LatticeRows.pointCopy_correct refs.pairNearest.wide.target.target.point
    refs.savedTarget separation.copy _ _ wide.target
  exact point_after_nearest refs _ _ _ copied
    separation.savedTargetAvoidsNearestWrites.first separation.savedTargetAvoidsNearestWrites.second
    separation.savedTargetAvoidsNearestWrites.third

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairNearestPlaneSavedTarget
