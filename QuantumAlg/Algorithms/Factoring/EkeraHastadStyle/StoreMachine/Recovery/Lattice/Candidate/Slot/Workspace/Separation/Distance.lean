/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Workspace.Separation.Checks

/-!
# Actual distance-prefix and complete candidate-slot separation
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotWorkspaceSeparation

open Execution
open LatticeCandidateSlotFrames

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {coordinateWidth modulusWidth : Nat}

private lemma distanceMaterializerSeparation
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (separation : FrameSeparation refs) :
    LatticeOffsetMaterializer.Separation refs.distance.materializer := by
  refine ⟨?_⟩
  intro left right equal
  exact MutableCell.offset.inj (separation.mutableKeyInjective equal)

private lemma distanceCandidateSeparation
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (separation : FrameSeparation refs) :
    LatticeShortLogCandidatePoint.Separation refs.distance.candidate := by
  refine ⟨⟨?_, ?_⟩⟩
  · intro source target
    cases source with
    | basisFirstFirst =>
      exact separation.externalAvoids (.candidateEntry .basisFirstFirst) (.candidate target)
    | basisFirstSecond =>
      exact separation.externalAvoids (.candidateEntry .basisFirstSecond) (.candidate target)
    | basisFirstThird =>
      exact separation.externalAvoids (.candidateEntry .basisFirstThird) (.candidate target)
    | basisSecondFirst =>
      exact separation.externalAvoids (.candidateEntry .basisSecondFirst) (.candidate target)
    | basisSecondSecond =>
      exact separation.externalAvoids (.candidateEntry .basisSecondSecond) (.candidate target)
    | basisSecondThird =>
      exact separation.externalAvoids (.candidateEntry .basisSecondThird) (.candidate target)
    | basisThirdFirst =>
      exact separation.externalAvoids (.candidateEntry .basisThirdFirst) (.candidate target)
    | basisThirdSecond =>
      exact separation.externalAvoids (.candidateEntry .basisThirdSecond) (.candidate target)
    | basisThirdThird =>
      exact separation.externalAvoids (.candidateEntry .basisThirdThird) (.candidate target)
    | centerFirst =>
      exact separation.externalAvoids (.candidateEntry .centerFirst) (.candidate target)
    | centerSecond =>
      exact separation.externalAvoids (.candidateEntry .centerSecond) (.candidate target)
    | centerThird =>
      exact separation.externalAvoids (.candidateEntry .centerThird) (.candidate target)
    | offsetFirst =>
      change mutableKey refs (.candidate target) ∉
        (LatticeState.coordinateInput refs.distance.candidate.offset.first).storageKeys
      rw [← refs.distance.materializerOffset]
      exact mutableInput_avoids refs separation refs.distance.materializer.offset.first
        (.offset .first) (.candidate target) rfl (by intro equal; cases equal)
    | offsetSecond =>
      change mutableKey refs (.candidate target) ∉
        (LatticeState.coordinateInput refs.distance.candidate.offset.second).storageKeys
      rw [← refs.distance.materializerOffset]
      exact mutableInput_avoids refs separation refs.distance.materializer.offset.second
        (.offset .second) (.candidate target) rfl (by intro equal; cases equal)
    | offsetThird =>
      change mutableKey refs (.candidate target) ∉
        (LatticeState.coordinateInput refs.distance.candidate.offset.third).storageKeys
      rw [← refs.distance.materializerOffset]
      exact mutableInput_avoids refs separation refs.distance.materializer.offset.third
        (.offset .third) (.candidate target) rfl (by intro equal; cases equal)
  · intro left right equal
    exact MutableCell.candidate.inj (separation.mutableKeyInjective equal)

private lemma candidatePoint_avoids
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (separation : FrameSeparation refs) (target : MutableCell)
    (first : MutableCell.candidate .pointFirst ≠ target)
    (second : MutableCell.candidate .pointSecond ≠ target)
    (third : MutableCell.candidate .pointThird ≠ target)
    (coordinate : LatticeCandidateDistancePrefix.PointCoordinate) :
    mutableKey refs target ∉
      (LatticeCandidateDistancePrefix.candidatePointInput
        refs.distance coordinate).storageKeys := by
  cases coordinate with
  | first =>
      exact mutableInput_avoids refs separation refs.distance.candidate.point.first
        (.candidate .pointFirst) target rfl first
  | second =>
      exact mutableInput_avoids refs separation refs.distance.candidate.point.second
        (.candidate .pointSecond) target rfl second
  | third =>
      exact mutableInput_avoids refs separation refs.distance.candidate.point.third
        (.candidate .pointThird) target rfl third

private lemma distanceSquaredSeparation
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (separation : FrameSeparation refs) :
    LatticeSquaredDistanceMachine.Separation refs.distance.distance := by
  have differenceSeparation :
      LatticePointDifferenceMachine.Separation refs.distance.distance.difference := by
    refine ⟨?_, ?_⟩
    · intro source target
      cases source with
      | pointFirst =>
        change mutableKey refs (.difference target) ∉
          (LatticeState.coordinateInput refs.distance.distance.difference.point.first).storageKeys
        rw [refs.distance.distancePoint]
        exact candidatePoint_avoids refs separation (.difference target)
          (by intro equal; cases equal) (by intro equal; cases equal)
          (by intro equal; cases equal) .first
      | pointSecond =>
        change mutableKey refs (.difference target) ∉
          (LatticeState.coordinateInput refs.distance.distance.difference.point.second).storageKeys
        rw [refs.distance.distancePoint]
        exact candidatePoint_avoids refs separation (.difference target)
          (by intro equal; cases equal) (by intro equal; cases equal)
          (by intro equal; cases equal) .second
      | pointThird =>
        change mutableKey refs (.difference target) ∉
          (LatticeState.coordinateInput refs.distance.distance.difference.point.third).storageKeys
        rw [refs.distance.distancePoint]
        exact candidatePoint_avoids refs separation (.difference target)
          (by intro equal; cases equal) (by intro equal; cases equal)
          (by intro equal; cases equal) .third
      | targetFirst =>
        change mutableKey refs (.difference target) ∉
          (LatticeState.coordinateInput refs.distance.distance.difference.target.first).storageKeys
        rw [refs.distance.distanceTarget]
        exact separation.externalAvoids (.originalTarget .first) (.difference target)
      | targetSecond =>
        change mutableKey refs (.difference target) ∉
          (LatticeState.coordinateInput refs.distance.distance.difference.target.second).storageKeys
        rw [refs.distance.distanceTarget]
        exact separation.externalAvoids (.originalTarget .second) (.difference target)
      | targetThird =>
        change mutableKey refs (.difference target) ∉
          (LatticeState.coordinateInput refs.distance.distance.difference.target.third).storageKeys
        rw [refs.distance.distanceTarget]
        exact separation.externalAvoids (.originalTarget .third) (.difference target)
    · intro left right equal
      exact MutableCell.difference.inj (separation.mutableKeyInjective equal)
  have coordinateSeparation (cell : LatticePointDifferenceMachine.DifferenceCell) :
      LatticeDot.CoordinateAccumulateSeparation
        (LatticeState.coordinateInput
          (LatticePointDifferenceMachine.differenceRef refs.distance.distance.difference cell))
        (LatticeState.coordinateInput
          (LatticePointDifferenceMachine.differenceRef refs.distance.distance.difference cell))
        refs.distance.distance.squaredDistance refs.distance.distance.product := by
    have differenceFree (target : MutableCell) (different : MutableCell.difference cell ≠ target) :
        mutableKey refs target ∉ (LatticeState.coordinateInput
          (LatticePointDifferenceMachine.differenceRef
            refs.distance.distance.difference cell)).storageKeys :=
      mutableInput_avoids refs separation _ (.difference cell) target rfl different
    exact ⟨differenceFree .distanceProduct (by intro equal; cases equal),
      differenceFree .distanceProduct (by intro equal; cases equal),
      mutableInput_avoids refs separation refs.distance.distance.squaredDistance
        .squaredDistance .distanceProduct rfl (by decide),
      differenceFree .squaredDistance (by intro equal; cases equal),
      differenceFree .squaredDistance (by intro equal; cases equal),
      mutableInput_avoids refs separation refs.distance.distance.product
        .distanceProduct .squaredDistance rfl (by decide)⟩
  exact ⟨differenceSeparation,
    ⟨coordinateSeparation .first, coordinateSeparation .second, coordinateSeparation .third⟩⟩

/-- All real component and cross-stage reads satisfy the original distance-prefix separation. -/
lemma distanceSeparation
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (separation : FrameSeparation refs) :
    LatticeCandidateDistancePrefix.Separation refs.distance := by
  refine ⟨distanceMaterializerSeparation refs separation,
    distanceCandidateSeparation refs separation,
    distanceSquaredSeparation refs separation, ?_, ?_, ?_, ?_⟩
  · exact fun source cell => separation.externalAvoids (.candidateEntry source) (.offset cell)
  · exact fun source cell => separation.externalAvoids (.originalTarget source) (.offset cell)
  · exact fun source cell => separation.externalAvoids (.originalTarget source) (.candidate cell)
  · intro coordinate
    exact ⟨candidatePoint_avoids refs separation (.difference .first)
        (by decide) (by decide) (by decide) coordinate,
      candidatePoint_avoids refs separation (.difference .second)
        (by decide) (by decide) (by decide) coordinate,
      candidatePoint_avoids refs separation (.difference .third)
        (by decide) (by decide) (by decide) coordinate,
      candidatePoint_avoids refs separation .squaredDistance
        (by decide) (by decide) (by decide) coordinate,
      candidatePoint_avoids refs separation .distanceProduct
        (by decide) (by decide) (by decide) coordinate⟩

/-- One common physical frame certificate supplies the five actual component separations. -/
lemma slotSeparation
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (separation : FrameSeparation refs) : LatticeCandidateSlotMachine.Separation refs :=
  ⟨distanceSeparation refs separation, nearTargetSeparation refs separation,
    exponentSeparation refs separation, powerSeparation refs separation,
    selectorSeparation refs separation⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotWorkspaceSeparation
