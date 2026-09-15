/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Offset.Loading.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Point.NearestPlane
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Distance.Resources

/-!
# Original candidate-distance wiring and live input frames
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateDistancePrefix

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)

noncomputable section

/-- Caller-owned cells for one materialized offset, candidate point, and distance. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- The literal three-coordinate offset materializer. -/
  materializer : LatticeOffsetMaterializer.Refs ctx width
  /-- The nearest-plane candidate-point adapter. -/
  candidate : LatticeShortLogCandidatePoint.Refs ctx width
  /-- The difference and squared-distance suffix. -/
  distance : LatticeSquaredDistanceMachine.Refs ctx width
  /-- Caller-owned target used only by the squared-distance suffix. -/
  originalTarget : LatticeState.PointRefs ctx width
  /-- The materializer writes exactly the candidate adapter's offset point. -/
  materializerOffset : materializer.offset = candidate.offset
  /-- The distance suffix reads exactly the candidate adapter's point. -/
  distancePoint : distance.difference.point = candidate.point
  /-- The distance suffix reads the caller-owned original target. -/
  distanceTarget : distance.difference.target = originalTarget

/-- The basis and center coordinates needed before the candidate-point stage. -/
inductive CandidateEntryCell where
  | basisFirstFirst | basisFirstSecond | basisFirstThird
  | basisSecondFirst | basisSecondSecond | basisSecondThird
  | basisThirdFirst | basisThirdSecond | basisThirdThird
  | centerFirst | centerSecond | centerThird
deriving DecidableEq

/-- One coordinate of a caller-owned point. -/
inductive PointCoordinate where
  | first | second | third
deriving DecidableEq

/-- Resolve one candidate-entry basis or center coordinate to a structural input. -/
def candidateEntryInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) :
    CandidateEntryCell → CInputRef ctx (.unsignedWord width)
  | .basisFirstFirst => LatticeState.coordinateInput refs.candidate.nearest.basis.first.first
  | .basisFirstSecond => LatticeState.coordinateInput refs.candidate.nearest.basis.first.second
  | .basisFirstThird => LatticeState.coordinateInput refs.candidate.nearest.basis.first.third
  | .basisSecondFirst => LatticeState.coordinateInput refs.candidate.nearest.basis.second.first
  | .basisSecondSecond => LatticeState.coordinateInput refs.candidate.nearest.basis.second.second
  | .basisSecondThird => LatticeState.coordinateInput refs.candidate.nearest.basis.second.third
  | .basisThirdFirst => LatticeState.coordinateInput refs.candidate.nearest.basis.third.first
  | .basisThirdSecond => LatticeState.coordinateInput refs.candidate.nearest.basis.third.second
  | .basisThirdThird => LatticeState.coordinateInput refs.candidate.nearest.basis.third.third
  | .centerFirst =>
      LatticeState.coordinateInput (LatticeShortLogCandidatePoint.centerRefs refs.candidate).first
  | .centerSecond =>
      LatticeState.coordinateInput (LatticeShortLogCandidatePoint.centerRefs refs.candidate).second
  | .centerThird =>
      LatticeState.coordinateInput (LatticeShortLogCandidatePoint.centerRefs refs.candidate).third

/-- Resolve a coordinate of the caller-owned original target. -/
def originalTargetInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) :
    PointCoordinate → CInputRef ctx (.unsignedWord width)
  | .first => LatticeState.coordinateInput refs.originalTarget.first
  | .second => LatticeState.coordinateInput refs.originalTarget.second
  | .third => LatticeState.coordinateInput refs.originalTarget.third

/-- Resolve a coordinate of the candidate point consumed by the distance suffix. -/
def candidatePointInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) :
    PointCoordinate → CInputRef ctx (.unsignedWord width)
  | .first => LatticeState.coordinateInput refs.candidate.point.first
  | .second => LatticeState.coordinateInput refs.candidate.point.second
  | .third => LatticeState.coordinateInput refs.candidate.point.third

/-- Caller reads outside the original offset materialization footprint. -/
def AvoidsMaterializerWrites {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    {shape : CShape} (refs : Refs ctx width) (input : CInputRef ctx shape) : Prop :=
  ∀ cell, LatticeOffsetMaterializer.mutableKey refs.materializer cell ∉ input.storageKeys

/-- Caller reads outside the original candidate-point construction footprint. -/
def AvoidsCandidateWrites {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    {shape : CShape} (refs : Refs ctx width) (input : CInputRef ctx shape) : Prop :=
  ∀ cell, LatticeCandidatePointMachine.mutableKey
    (LatticeShortLogCandidatePoint.candidateRefs refs.candidate) cell ∉ input.storageKeys

/-- Caller reads outside the original difference, distance and product destinations. -/
def AvoidsDistanceWrites {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    {shape : CShape} (refs : Refs ctx width) (input : CInputRef ctx shape) : Prop :=
  refs.distance.difference.difference.first.key ∉ input.storageKeys ∧
    refs.distance.difference.difference.second.key ∉ input.storageKeys ∧
      refs.distance.difference.difference.third.key ∉ input.storageKeys ∧
        refs.distance.squaredDistance.key ∉ input.storageKeys ∧
          refs.distance.product.key ∉ input.storageKeys

/-- Complete component and cross-stage separation for the three-phase prefix. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  materializer : LatticeOffsetMaterializer.Separation refs.materializer
  candidate : LatticeShortLogCandidatePoint.Separation refs.candidate
  distance : LatticeSquaredDistanceMachine.Separation refs.distance
  candidateEntryAvoidsMaterializer : ∀ cell,
    AvoidsMaterializerWrites refs (candidateEntryInput refs cell)
  originalTargetAvoidsMaterializer : ∀ coordinate,
    AvoidsMaterializerWrites refs (originalTargetInput refs coordinate)
  originalTargetAvoidsCandidate : ∀ coordinate,
    AvoidsCandidateWrites refs (originalTargetInput refs coordinate)
  candidatePointAvoidsDistance : ∀ coordinate,
    AvoidsDistanceWrites refs (candidatePointInput refs coordinate)

/-! ## Original mathematical inputs and actual caller frame -/

/-- Raw representations needed before the offset materializer starts. -/
structure InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (m ell : Nat) (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (originalTarget : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (before : Store ctx) : Prop where
  basis : LatticeCandidatePointMachine.BasisRawRepresents before refs.candidate.nearest.basis
    (LatticeNearestPlaneShortLog.basis m ell samples)
  center : LatticeArithmetic.PointRawRepresents before
    (LatticeShortLogCandidatePoint.centerRefs refs.candidate)
      (LatticeNearestPlaneShortLog.trace m ell samples).center
  originalTarget : LatticeArithmetic.PointRawRepresents before refs.originalTarget originalTarget

/-- Reads outside all three phase footprints are preserved. -/
def CallerFrame {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    AvoidsMaterializerWrites refs other →
      AvoidsCandidateWrites refs other →
        AvoidsDistanceWrites refs other → after.read other = before.read other


end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateDistancePrefix
