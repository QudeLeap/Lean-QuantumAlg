/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Dot.Refresh
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Gram.Norm
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv

/-!
# Caller layout for first-coordinate nearest-plane reduction

The original raw integer range, positive norm and separation conditions govern
actual storage. Neither a scratch initializer nor an alternative evaluator is
part of the caller contract.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneFirst

open ClassicalRoutines.NumberTheory
open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

/-- Caller-owned cells for one raw nearest-plane first-coordinate reduction. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Nested references for the basis stage. -/
  basis : LatticeState.BasisRefs ctx width
  /-- Nested references for the target stage. -/
  target : LatticeState.PointRefs ctx width
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

/-- All three coordinate reads of a point avoid one selected storage key. -/
structure PointInputAvoidsKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (point : LatticeState.PointRefs ctx width) (key : StorageKey) : Prop where
  first : key ∉ (LatticeState.coordinateInput point.first).storageKeys
  second : key ∉ (LatticeState.coordinateInput point.second).storageKeys
  third : key ∉ (LatticeState.coordinateInput point.third).storageKeys

/-- The dot-refresh view that overwrites the first-coordinate numerator. -/
def numeratorDotRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : LatticeDotRefresh.Refs ctx width where
  dot := refs.numerator
  dotRole := refs.numeratorRole
  product := refs.dotProduct
  productRole := refs.dotProductRole

/-- The norm-refresh view that overwrites the positive first-coordinate denominator. -/
def denominatorNormRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : LatticeNormRefresh.Refs ctx width where
  norm := refs.denominator
  normRole := refs.denominatorRole
  product := refs.normProduct
  productRole := refs.normProductRole

/-- The phase-local separation data needed by the semantic proof. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  numeratorDot : LatticeDotRefresh.Separation refs.target refs.basis.first
    (numeratorDotRefs refs)
  denominatorNorm : LatticeNormRefresh.Separation refs.basis.first
    (denominatorNormRefs refs)
  numeratorAvoidsDenominator :
    refs.denominator.key ∉ (SignedWord.writeInput refs.numerator).storageKeys
  numeratorAvoidsNormProduct :
    refs.normProduct.key ∉ (SignedWord.writeInput refs.numerator).storageKeys
  targetAvoidsDenominator :
    PointInputAvoidsKey refs.target refs.denominator.toCStorageRef.key
  targetAvoidsNormProduct :
    PointInputAvoidsKey refs.target refs.normProduct.toCStorageRef.key
  basisFirstAvoidsDivision :
    ∀ key ∈ SignedWord.RoundedDiv.mutableKeys refs.division,
      PointInputAvoidsKey refs.basis.first key
  targetAvoidsDivision :
    ∀ key ∈ SignedWord.RoundedDiv.mutableKeys refs.division,
      PointInputAvoidsKey refs.target key
  division : SignedWord.RoundedDiv.Separation refs.division
  reduction : LatticeArithmetic.PointReduceSeparation
    (SignedWord.writeInput refs.division.output) refs.basis.first refs.target
      refs.reduceProduct

/-- The target-to-first-row dot product used by the first-coordinate numerator. -/
def numeratorValue (targetValue firstValue : NumberTheory.IntegerPoint3) : Int :=
  NumberTheory.integerPointDot targetValue firstValue

/-- The first-row squared norm used as the positive division denominator. -/
def denominatorValue (firstValue : NumberTheory.IntegerPoint3) : Int :=
  NumberTheory.integerPointSquaredNorm firstValue

/-- No-wrap hypotheses for the nearest-plane integer target. -/
structure Fits (width : Nat) (firstValue targetValue : NumberTheory.IntegerPoint3) : Prop where
  widthPositive : 0 < width
  numeratorRange :
    ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable width
      (numeratorValue targetValue firstValue)
  denominatorFits : NumberTheory.integerPointSquaredNorm firstValue < CShape.wordModulus width

/-- Entry data for the semantic theorem; the literal body has no scratch-zero premise. -/
def InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (before : Store ctx) (refs : Refs ctx width)
    (firstValue targetValue : NumberTheory.IntegerPoint3) : Prop :=
  LatticeArithmetic.PointRawRepresents before refs.basis.first firstValue ∧
    LatticeArithmetic.PointRawRepresents before refs.target targetValue ∧
      Fits width firstValue targetValue

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneFirst
