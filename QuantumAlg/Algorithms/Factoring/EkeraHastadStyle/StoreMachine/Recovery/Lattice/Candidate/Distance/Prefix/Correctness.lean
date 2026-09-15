/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Distance.Prefix

/-!
# Actual original candidate point and squared-distance correctness

Every mathematical premise refers to the actual incoming store. The original
basis and center survive offset loading; the original target survives both
loading and candidate construction. Squared distance initializes itself.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateDistancePrefix

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original candidate point, difference and squared norm with the full caller frame. -/
structure Outcome (m ell : Nat) (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (offset originalTarget : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (before after : Store ctx) : Prop where
  point : LatticeArithmetic.PointRawRepresents after refs.candidate.point
    (RSA.shortLogPointAtOffset m ell samples offset)
  difference : LatticeArithmetic.PointRawRepresents after refs.distance.difference.difference
    ((RSA.shortLogPointAtOffset m ell samples offset).sub originalTarget)
  squaredDistance : RawSignedRepresents
    (after.read (LatticeArithmetic.writeInput refs.distance.squaredDistance))
    (NumberTheory.integerPointSquaredNorm
      ((RSA.shortLogPointAtOffset m ell samples offset).sub originalTarget) : Int)
  callerFrame : CallerFrame refs before after

/-- The actual three-phase prefix realizes the original source candidate and squared distance. -/
theorem candidateDistancePrefixInto_correct (m ell : Nat)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (offset originalTarget : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (separation : Separation refs) (store : Store ctx)
    (initial : InitialConditions m ell samples originalTarget refs store) :
    Outcome m ell samples offset originalTarget refs store (prefixStep offset refs store).1 := by
  let materialized := (LatticeOffsetMaterializer.setOffsetStep offset refs.materializer store).1
  let constructed := (LatticeShortLogCandidatePoint.candidateStep refs.candidate materialized).1
  let finalStore := (LatticeSquaredDistanceMachine.distanceStep refs.distance constructed).1
  have materializerHolds := LatticeOffsetMaterializer.setOffsetInto_correct offset refs.materializer
    separation.materializer store
  have materializerFrame {shape : CShape} (other : CInputRef ctx shape)
      (avoids : AvoidsMaterializerWrites refs other) : materialized.read other = store.read other :=
    LatticeOffsetMaterializer.setOffsetInto_callerFrame offset refs.materializer store other avoids
  have candidateFrame {shape : CShape} (other : CInputRef ctx shape)
      (avoids : AvoidsCandidateWrites refs other) :
      constructed.read other = materialized.read other :=
    LatticeShortLogCandidatePoint.candidatePointInto_callerFrame refs.candidate materialized other
      avoids
  have distanceFrame {shape : CShape} (other : CInputRef ctx shape)
      (avoids : AvoidsDistanceWrites refs other) : finalStore.read other = constructed.read other :=
    LatticeSquaredDistanceMachine.squaredDistanceInto_callerFrame refs.distance constructed other
      avoids.1 avoids.2.1 avoids.2.2.1 avoids.2.2.2.1 avoids.2.2.2.2
  have candidateEntryAtMaterializer (cell : CandidateEntryCell) (value : Int)
      (represented : RawSignedRepresents
        (store.read (candidateEntryInput refs cell)) value) :
      RawSignedRepresents
        (materialized.read (candidateEntryInput refs cell)) value := by
    rw [materializerFrame _ (separation.candidateEntryAvoidsMaterializer cell)]
    exact represented
  have originalTargetAtMaterializer (coordinate : PointCoordinate) (value : Int)
      (represented : RawSignedRepresents
        (store.read (originalTargetInput refs coordinate)) value) :
      RawSignedRepresents
        (materialized.read (originalTargetInput refs coordinate)) value := by
    rw [materializerFrame _ (separation.originalTargetAvoidsMaterializer coordinate)]
    exact represented
  rcases initial.basis with ⟨basisFirst, basisSecond, basisThird⟩
  rcases basisFirst with ⟨basisFirstFirst, basisFirstSecond, basisFirstThird⟩
  rcases basisSecond with ⟨basisSecondFirst, basisSecondSecond, basisSecondThird⟩
  rcases basisThird with ⟨basisThirdFirst, basisThirdSecond, basisThirdThird⟩
  have basisAtCandidate : LatticeCandidatePointMachine.BasisRawRepresents
      materialized refs.candidate.nearest.basis
      (LatticeNearestPlaneShortLog.basis m ell samples) := by
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · exact candidateEntryAtMaterializer .basisFirstFirst _ basisFirstFirst
    · exact candidateEntryAtMaterializer .basisFirstSecond _ basisFirstSecond
    · exact candidateEntryAtMaterializer .basisFirstThird _ basisFirstThird
    · exact candidateEntryAtMaterializer .basisSecondFirst _ basisSecondFirst
    · exact candidateEntryAtMaterializer .basisSecondSecond _ basisSecondSecond
    · exact candidateEntryAtMaterializer .basisSecondThird _ basisSecondThird
    · exact candidateEntryAtMaterializer .basisThirdFirst _ basisThirdFirst
    · exact candidateEntryAtMaterializer .basisThirdSecond _ basisThirdSecond
    · exact candidateEntryAtMaterializer .basisThirdThird _ basisThirdThird
  rcases initial.center with ⟨centerFirst, centerSecond, centerThird⟩
  have centerAtCandidate : LatticeArithmetic.PointRawRepresents
      materialized
      (LatticeShortLogCandidatePoint.centerRefs refs.candidate)
      (LatticeNearestPlaneShortLog.trace m ell samples).center := by
    refine ⟨?_, ?_, ?_⟩
    · exact candidateEntryAtMaterializer .centerFirst _ centerFirst
    · exact candidateEntryAtMaterializer .centerSecond _ centerSecond
    · exact candidateEntryAtMaterializer .centerThird _ centerThird
  have offsetAtCandidate : LatticeArithmetic.PointRawRepresents
      materialized refs.candidate.offset offset := by
    rw [← refs.materializerOffset]
    exact materializerHolds.offset
  have candidateInitial : LatticeShortLogCandidatePoint.InitialConditions m ell samples
      offset refs.candidate materialized :=
    ⟨basisAtCandidate, centerAtCandidate, offsetAtCandidate⟩
  have candidateHolds := LatticeShortLogCandidatePoint.candidatePointInto_correct m ell samples
    offset refs.candidate separation.candidate materialized candidateInitial
  have candidatePointAtDistance := candidateHolds.point
  rcases initial.originalTarget with ⟨targetFirst, targetSecond, targetThird⟩
  have originalTargetAtCandidate : LatticeArithmetic.PointRawRepresents
      materialized refs.originalTarget originalTarget := by
    refine ⟨?_, ?_, ?_⟩
    · exact originalTargetAtMaterializer .first _ targetFirst
    · exact originalTargetAtMaterializer .second _ targetSecond
    · exact originalTargetAtMaterializer .third _ targetThird
  have originalTargetAtDistance : LatticeArithmetic.PointRawRepresents
      constructed refs.originalTarget originalTarget := by
    rcases originalTargetAtCandidate with ⟨targetFirst, targetSecond, targetThird⟩
    refine ⟨?_, ?_, ?_⟩
    · change RawSignedRepresents
        (constructed.read
          (originalTargetInput refs .first)) originalTarget.1
      rw [candidateFrame _ (separation.originalTargetAvoidsCandidate .first)]
      exact targetFirst
    · change RawSignedRepresents
        (constructed.read
          (originalTargetInput refs .second)) originalTarget.2.1
      rw [candidateFrame _ (separation.originalTargetAvoidsCandidate .second)]
      exact targetSecond
    · change RawSignedRepresents
        (constructed.read
          (originalTargetInput refs .third)) originalTarget.2.2
      rw [candidateFrame _ (separation.originalTargetAvoidsCandidate .third)]
      exact targetThird
  have candidatePointForDistance : LatticeArithmetic.PointRawRepresents
      constructed refs.distance.difference.point
      (RSA.shortLogPointAtOffset m ell samples offset) := by
    rw [refs.distancePoint]
    exact candidatePointAtDistance
  have targetForDistance : LatticeArithmetic.PointRawRepresents
      constructed refs.distance.difference.target
      originalTarget := by
    rw [refs.distanceTarget]
    exact originalTargetAtDistance
  have distanceInitial : LatticeSquaredDistanceMachine.InitialConditions
      constructed refs.distance
      (RSA.shortLogPointAtOffset m ell samples offset) originalTarget :=
    ⟨candidatePointForDistance, targetForDistance⟩
  have distanceHolds := LatticeSquaredDistanceMachine.squaredDistanceInto_correct refs.distance
    separation.distance constructed (RSA.shortLogPointAtOffset m ell samples offset)
    originalTarget distanceInitial
  have candidatePointAtFinal : LatticeArithmetic.PointRawRepresents
      finalStore refs.candidate.point
      (RSA.shortLogPointAtOffset m ell samples offset) := by
    rcases candidatePointAtDistance with ⟨pointFirst, pointSecond, pointThird⟩
    refine ⟨?_, ?_, ?_⟩
    · change RawSignedRepresents
        (finalStore.read
          (candidatePointInput refs .first))
          (RSA.shortLogPointAtOffset m ell samples offset).1
      rw [distanceFrame _ (separation.candidatePointAvoidsDistance .first)]
      exact pointFirst
    · change RawSignedRepresents
        (finalStore.read
          (candidatePointInput refs .second))
          (RSA.shortLogPointAtOffset m ell samples offset).2.1
      rw [distanceFrame _ (separation.candidatePointAvoidsDistance .second)]
      exact pointSecond
    · change RawSignedRepresents
        (finalStore.read
          (candidatePointInput refs .third))
          (RSA.shortLogPointAtOffset m ell samples offset).2.2
      rw [distanceFrame _ (separation.candidatePointAvoidsDistance .third)]
      exact pointThird
  exact ⟨candidatePointAtFinal, distanceHolds.difference, distanceHolds.squaredDistance,
    candidateDistancePrefixInto_callerFrame offset refs store⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateDistancePrefix
