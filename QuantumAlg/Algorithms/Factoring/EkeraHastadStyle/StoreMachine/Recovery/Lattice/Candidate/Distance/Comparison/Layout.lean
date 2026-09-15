/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Coordinate
import all QuantumAlg.Components.Classical.Word.PowerOfTwo.Resources

/-!
# Original near-target comparison cells and bounds
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearTargetScale

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)

noncomputable section

/-- Original caller-owned words and flag for the scaled near-target comparison. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Input reference for the distance value. -/
  distance : CInputRef ctx (.unsignedWord width)
  /-- Input reference for the upper bound value. -/
  upperBound : CInputRef ctx (.unsignedWord width)
  /-- Writable cell for the scaled distance value. -/
  scaledDistance : CWriteRef ctx (.unsignedWord width)
  scaledDistanceRole : scaledDistance.toCStorageRef.role = .workspace
  /-- Writable cell for the range square value. -/
  rangeSquare : CWriteRef ctx (.unsignedWord width)
  rangeSquareRole : rangeSquare.toCStorageRef.role = .workspace
  /-- Writable cell for the scaled range value. -/
  scaledRange : CWriteRef ctx (.unsignedWord width)
  scaledRangeRole : scaledRange.toCStorageRef.role = .workspace
  /-- Writable cell for the accepted value. -/
  accepted : CWriteRef ctx .bit
  acceptedRole : accepted.toCStorageRef.role = .workspace

/-- The original distance and upper-bound input words. -/
inductive SourceCell where | distance | upperBound deriving DecidableEq
/-- The four original comparison destinations. -/
inductive MutableCell where | scaledDistance | rangeSquare | scaledRange | accepted
  deriving DecidableEq

/-- Resolve an original structural comparison input. -/
def sourceInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : SourceCell → CInputRef ctx (.unsignedWord width)
  | .distance => refs.distance
  | .upperBound => refs.upperBound

/-- Actual storage identity of each original destination. -/
def mutableKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : MutableCell → StorageKey
  | .scaledDistance => refs.scaledDistance.toCStorageRef.key
  | .rangeSquare => refs.rangeSquare.toCStorageRef.key
  | .scaledRange => refs.scaledRange.toCStorageRef.key
  | .accepted => refs.accepted.toCStorageRef.key

/-- Original source-versus-write and write-versus-write separation. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  sourceAvoidsMutable : ∀ source cell,
    mutableKey refs cell ∉ (sourceInput refs source).storageKeys
  mutableInjective : Function.Injective (mutableKey refs)

/-- Original raw inputs and exact unsigned bounds for the final comparison operands. -/
structure InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (before : Store ctx) (refs : Refs ctx width)
    (distance upperBound : Nat) : Prop where
  distanceRaw : RawSignedRepresents (before.read refs.distance) (distance : Int)
  upperBoundRaw : RawSignedRepresents (before.read refs.upperBound) (upperBound : Int)
  distanceFits : distance < CShape.wordModulus width
  upperBoundFits : upperBound < CShape.wordModulus width
  scaledDistanceFits : 8 * distance < CShape.wordModulus width
  rangeSquareFits : upperBound * upperBound < CShape.wordModulus width
  scaledRangeFits : 9 * (upperBound * upperBound) < CShape.wordModulus width


end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearTargetScale
