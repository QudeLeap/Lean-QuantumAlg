/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Third.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Second.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Second.Frame
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.First.Correctness

/-!
# Actual three-stage nearest-plane layout

All phases share the original basis and residual target. Phase-local separation
already protects the needed basis rows; only retained coefficients need explicit
cross-phase frame premises.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThree

open ClassicalRoutines.NumberTheory
open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

/-- Scratch storage owned only by the third-coordinate phase. -/
structure ThirdScratchRefs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Nested references for the cross stage. -/
  cross : LatticeState.PointRefs ctx width
  /-- Writable cell for the product left value. -/
  productLeft : CWriteRef ctx (LatticeState.RawSignedWordShape width)
  productLeftRole : productLeft.toCStorageRef.role = .workspace
  /-- Writable cell for the product right value. -/
  productRight : CWriteRef ctx (LatticeState.RawSignedWordShape width)
  productRightRole : productRight.toCStorageRef.role = .workspace
  /-- Writable cell for the dot product value. -/
  dotProduct : CWriteRef ctx (.unsignedWord width)
  dotProductRole : dotProduct.toCStorageRef.role = .workspace
  /-- Writable cell for the numerator value. -/
  numerator : CWriteRef ctx (.unsignedWord width)
  numeratorRole : numerator.toCStorageRef.role = .workspace
  /-- Writable cell for the denominator value. -/
  denominator : CWriteRef ctx (.unsignedWord width)
  denominatorRole : denominator.toCStorageRef.role = .workspace
  /-- Writable cell for the denominator magnitude value. -/
  denominatorMagnitude : CWriteRef ctx (.unsignedWord width)
  denominatorMagnitudeRole : denominatorMagnitude.toCStorageRef.role = .workspace
  /-- Nested references for the division stage. -/
  division : SignedWord.RoundedDiv.BodyRefs ctx width
  /-- Writable cell for the reduce product value. -/
  reduceProduct : CWriteRef ctx (.unsignedWord width)
  reduceProductRole : reduceProduct.toCStorageRef.role = .workspace
  divisionNumerator : division.numerator = SignedWord.writeInput numerator
  divisionDenominator : division.denominator = SignedWord.writeInput denominatorMagnitude

/-- Scratch storage owned only by the second-coordinate phase. -/
structure SecondScratchRefs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Nested references for the cross stage. -/
  cross : LatticeState.PointRefs ctx width
  /-- Writable cell for the cross product left value. -/
  crossProductLeft : CWriteRef ctx (LatticeState.RawSignedWordShape width)
  crossProductLeftRole : crossProductLeft.toCStorageRef.role = .workspace
  /-- Writable cell for the cross product right value. -/
  crossProductRight : CWriteRef ctx (LatticeState.RawSignedWordShape width)
  crossProductRightRole : crossProductRight.toCStorageRef.role = .workspace
  /-- Writable cell for the dot product value. -/
  dotProduct : CWriteRef ctx (.unsignedWord width)
  dotProductRole : dotProduct.toCStorageRef.role = .workspace
  /-- Writable cell for the g 11 value. -/
  g11 : CWriteRef ctx (.unsignedWord width)
  g11Role : g11.toCStorageRef.role = .workspace
  /-- Writable cell for the g 21 value. -/
  g21 : CWriteRef ctx (.unsignedWord width)
  g21Role : g21.toCStorageRef.role = .workspace
  /-- Writable cell for the target dot second value. -/
  targetDotSecond : CWriteRef ctx (.unsignedWord width)
  targetDotSecondRole : targetDotSecond.toCStorageRef.role = .workspace
  /-- Writable cell for the target dot first value. -/
  targetDotFirst : CWriteRef ctx (.unsignedWord width)
  targetDotFirstRole : targetDotFirst.toCStorageRef.role = .workspace
  /-- Writable cell for the numerator value. -/
  numerator : CWriteRef ctx (.unsignedWord width)
  numeratorRole : numerator.toCStorageRef.role = .workspace
  /-- Writable cell for the numerator product value. -/
  numeratorProduct : CWriteRef ctx (.unsignedWord width)
  numeratorProductRole : numeratorProduct.toCStorageRef.role = .workspace
  /-- Writable cell for the denominator value. -/
  denominator : CWriteRef ctx (.unsignedWord width)
  denominatorRole : denominator.toCStorageRef.role = .workspace
  /-- Nested references for the division stage. -/
  division : SignedWord.RoundedDiv.BodyRefs ctx width
  /-- Writable cell for the reduce product value. -/
  reduceProduct : CWriteRef ctx (.unsignedWord width)
  reduceProductRole : reduceProduct.toCStorageRef.role = .workspace
  divisionNumerator : division.numerator = SignedWord.writeInput numerator
  divisionDenominator : division.denominator = SignedWord.writeInput denominator

/-- Scratch storage owned only by the first-coordinate phase. -/
structure FirstScratchRefs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Writable cell for the dot product value. -/
  dotProduct : CWriteRef ctx (.unsignedWord width)
  dotProductRole : dotProduct.toCStorageRef.role = .workspace
  /-- Writable cell for the numerator value. -/
  numerator : CWriteRef ctx (.unsignedWord width)
  numeratorRole : numerator.toCStorageRef.role = .workspace
  /-- Writable cell for the norm product value. -/
  normProduct : CWriteRef ctx (.unsignedWord width)
  normProductRole : normProduct.toCStorageRef.role = .workspace
  /-- Writable cell for the denominator value. -/
  denominator : CWriteRef ctx (.unsignedWord width)
  denominatorRole : denominator.toCStorageRef.role = .workspace
  /-- Nested references for the division stage. -/
  division : SignedWord.RoundedDiv.BodyRefs ctx width
  /-- Writable cell for the reduce product value. -/
  reduceProduct : CWriteRef ctx (.unsignedWord width)
  reduceProductRole : reduceProduct.toCStorageRef.role = .workspace
  divisionNumerator : division.numerator = SignedWord.writeInput numerator
  divisionDenominator : division.denominator = SignedWord.writeInput denominator

/-- Common input and phase-local scratch storage for the three reductions. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Nested references for the basis stage. -/
  basis : LatticeState.BasisRefs ctx width
  /-- Nested references for the target stage. -/
  target : LatticeState.PointRefs ctx width
  /-- Nested references for the third stage. -/
  third : ThirdScratchRefs ctx width
  /-- Nested references for the second stage. -/
  second : SecondScratchRefs ctx width
  /-- Nested references for the first stage. -/
  first : FirstScratchRefs ctx width

/-- The third-phase view with the common basis and target references. -/
def thirdRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : LatticeNearestPlaneThird.Refs ctx width where
  basis := refs.basis
  target := refs.target
  cross := refs.third.cross
  productLeft := refs.third.productLeft
  productLeftRole := refs.third.productLeftRole
  productRight := refs.third.productRight
  productRightRole := refs.third.productRightRole
  dotProduct := refs.third.dotProduct
  dotProductRole := refs.third.dotProductRole
  numerator := refs.third.numerator
  numeratorRole := refs.third.numeratorRole
  denominator := refs.third.denominator
  denominatorRole := refs.third.denominatorRole
  denominatorMagnitude := refs.third.denominatorMagnitude
  denominatorMagnitudeRole := refs.third.denominatorMagnitudeRole
  division := refs.third.division
  reduceProduct := refs.third.reduceProduct
  reduceProductRole := refs.third.reduceProductRole
  divisionNumerator := refs.third.divisionNumerator
  divisionDenominator := refs.third.divisionDenominator

/-- The second-phase view with the common basis and target references. -/
def secondRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : LatticeNearestPlaneSecond.Refs ctx width where
  basis := refs.basis
  target := refs.target
  cross := refs.second.cross
  crossProductLeft := refs.second.crossProductLeft
  crossProductLeftRole := refs.second.crossProductLeftRole
  crossProductRight := refs.second.crossProductRight
  crossProductRightRole := refs.second.crossProductRightRole
  dotProduct := refs.second.dotProduct
  dotProductRole := refs.second.dotProductRole
  g11 := refs.second.g11
  g11Role := refs.second.g11Role
  g21 := refs.second.g21
  g21Role := refs.second.g21Role
  targetDotSecond := refs.second.targetDotSecond
  targetDotSecondRole := refs.second.targetDotSecondRole
  targetDotFirst := refs.second.targetDotFirst
  targetDotFirstRole := refs.second.targetDotFirstRole
  numerator := refs.second.numerator
  numeratorRole := refs.second.numeratorRole
  numeratorProduct := refs.second.numeratorProduct
  numeratorProductRole := refs.second.numeratorProductRole
  denominator := refs.second.denominator
  denominatorRole := refs.second.denominatorRole
  division := refs.second.division
  reduceProduct := refs.second.reduceProduct
  reduceProductRole := refs.second.reduceProductRole
  divisionNumerator := refs.second.divisionNumerator
  divisionDenominator := refs.second.divisionDenominator

/-- The first-phase view with the common basis and target references. -/
def firstRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : LatticeNearestPlaneFirst.Refs ctx width where
  basis := refs.basis
  target := refs.target
  dotProduct := refs.first.dotProduct
  dotProductRole := refs.first.dotProductRole
  numerator := refs.first.numerator
  numeratorRole := refs.first.numeratorRole
  normProduct := refs.first.normProduct
  normProductRole := refs.first.normProductRole
  denominator := refs.first.denominator
  denominatorRole := refs.first.denominatorRole
  division := refs.first.division
  reduceProduct := refs.first.reduceProduct
  reduceProductRole := refs.first.reduceProductRole
  divisionNumerator := refs.first.divisionNumerator
  divisionDenominator := refs.first.divisionDenominator

/-- Caller reads outside all actual third-phase writes. -/
abbrev ThirdFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    {shape : CShape} (refs : Refs ctx width) (other : CInputRef ctx shape) : Prop :=
  ∀ cell ∈ LatticeNearestPlaneThird.mutableCells,
    LatticeNearestPlaneThird.phaseCellKey (thirdRefs refs) cell ∉ other.storageKeys

/-- Caller reads outside all actual second-phase writes. -/
abbrev SecondFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    {shape : CShape} (refs : Refs ctx width) (other : CInputRef ctx shape) : Prop :=
  ∀ key ∈ LatticeNearestPlaneSecond.mutableKeys (secondRefs refs), key ∉ other.storageKeys

/-- Caller reads outside all actual first-phase writes. -/
structure FirstFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    {shape : CShape} (refs : Refs ctx width) (other : CInputRef ctx shape) : Prop where
  dotProduct : refs.first.dotProduct.key ∉ other.storageKeys
  numerator : refs.first.numerator.key ∉ other.storageKeys
  normProduct : refs.first.normProduct.key ∉ other.storageKeys
  denominator : refs.first.denominator.key ∉ other.storageKeys
  division : ∀ key ∈ RoundedDiv.mutableKeys refs.first.division, key ∉ other.storageKeys
  reduceProduct : refs.first.reduceProduct.key ∉ other.storageKeys
  targetFirst : refs.target.first.key ∉ other.storageKeys
  targetSecond : refs.target.second.key ∉ other.storageKeys
  targetThird : refs.target.third.key ∉ other.storageKeys

/-- A caller read outside the written footprint of all three actual phases. -/
structure FrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    {shape : CShape} (refs : Refs ctx width) (other : CInputRef ctx shape) : Prop where
  third : ThirdFrameAvoids refs other
  second : SecondFrameAvoids refs other
  first : FirstFrameAvoids refs other

/-- Phase-local separation and the three required cross-phase coefficient frames. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  third : LatticeNearestPlaneThird.Separation (thirdRefs refs)
  second : LatticeNearestPlaneSecond.Separation (secondRefs refs)
  first : LatticeNearestPlaneFirst.Separation (firstRefs refs)
  secondPreservesThirdOutput : SecondFrameAvoids refs (writeInput refs.third.division.output)
  firstPreservesThirdOutput : FirstFrameAvoids refs (writeInput refs.third.division.output)
  firstPreservesSecondOutput : FirstFrameAvoids refs (writeInput refs.second.division.output)

/-- Original numeric domains of the three actual nearest-plane reductions. -/
structure Fits (width : Nat) (basis : NumberTheory.IntegerBasis3)
    (target : NumberTheory.IntegerPoint3) : Prop where
  third : LatticeNearestPlaneThird.Fits width basis.first basis.second basis.third target
  second : LatticeNearestPlaneSecond.Fits width basis target
  first : LatticeNearestPlaneFirst.Fits width basis.first
    (LatticeNearestPlaneResidual.afterSecond basis target)
  firstDenominatorNonzero : LatticeNearestPlaneFirst.denominatorValue basis.first ≠ 0

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThree
