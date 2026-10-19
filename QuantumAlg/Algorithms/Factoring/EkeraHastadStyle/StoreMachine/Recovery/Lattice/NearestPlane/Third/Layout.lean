/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Cross.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Cross.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Dot.Refresh
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Residual
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Correctness

/-!
# Actual third-coordinate nearest-plane layout

The caller's original cells and integer domains are retained. Signed denominator
normalization and the coefficient are computed from the actual stored words.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird

open ClassicalRoutines.NumberTheory
open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

/-- Caller-owned cells for one raw nearest-plane third-coordinate reduction. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Nested references for the basis stage. -/
  basis : LatticeState.BasisRefs ctx width
  /-- Nested references for the target stage. -/
  target : LatticeState.PointRefs ctx width
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

/-- The dot-refresh view that overwrites the third-coordinate numerator. -/
def numeratorDotRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : LatticeDotRefresh.Refs ctx width where
  dot := refs.numerator
  dotRole := refs.numeratorRole
  product := refs.dotProduct
  productRole := refs.dotProductRole

/-- The dot-refresh view that overwrites the signed third-coordinate denominator. -/
def denominatorDotRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : LatticeDotRefresh.Refs ctx width where
  dot := refs.denominator
  dotRole := refs.denominatorRole
  product := refs.dotProduct
  productRole := refs.dotProductRole

/-- Named cells whose pairwise separation supports the complete third phase. -/
inductive PhaseCell where
  | basisFirstFirst | basisFirstSecond | basisFirstThird
  | basisSecondFirst | basisSecondSecond | basisSecondThird
  | basisThirdFirst | basisThirdSecond | basisThirdThird
  | targetFirst | targetSecond | targetThird
  | crossFirst | crossSecond | crossThird
  | productLeft | productRight | dotProduct | numerator | denominator
  | denominatorMagnitude
  | divisionMagnitude | divisionNegative | divisionWideNumerator
  | divisionWideDenominator | divisionQuotientRemainder | divisionOutput
  | reduceProduct
deriving DecidableEq

/-- Resolve one named third-phase cell to its caller-owned storage key. -/
def phaseCellKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : PhaseCell → StorageKey
  | .basisFirstFirst => refs.basis.first.first.toCStorageRef.key
  | .basisFirstSecond => refs.basis.first.second.toCStorageRef.key
  | .basisFirstThird => refs.basis.first.third.toCStorageRef.key
  | .basisSecondFirst => refs.basis.second.first.toCStorageRef.key
  | .basisSecondSecond => refs.basis.second.second.toCStorageRef.key
  | .basisSecondThird => refs.basis.second.third.toCStorageRef.key
  | .basisThirdFirst => refs.basis.third.first.toCStorageRef.key
  | .basisThirdSecond => refs.basis.third.second.toCStorageRef.key
  | .basisThirdThird => refs.basis.third.third.toCStorageRef.key
  | .targetFirst => refs.target.first.toCStorageRef.key
  | .targetSecond => refs.target.second.toCStorageRef.key
  | .targetThird => refs.target.third.toCStorageRef.key
  | .crossFirst => refs.cross.first.toCStorageRef.key
  | .crossSecond => refs.cross.second.toCStorageRef.key
  | .crossThird => refs.cross.third.toCStorageRef.key
  | .productLeft => refs.productLeft.toCStorageRef.key
  | .productRight => refs.productRight.toCStorageRef.key
  | .dotProduct => refs.dotProduct.toCStorageRef.key
  | .numerator => refs.numerator.toCStorageRef.key
  | .denominator => refs.denominator.toCStorageRef.key
  | .denominatorMagnitude => refs.denominatorMagnitude.toCStorageRef.key
  | .divisionMagnitude => refs.division.magnitude.toCStorageRef.key
  | .divisionNegative => refs.division.negative.toCStorageRef.key
  | .divisionWideNumerator => refs.division.wideNumerator.toCStorageRef.key
  | .divisionWideDenominator => refs.division.wideDenominator.toCStorageRef.key
  | .divisionQuotientRemainder => refs.division.division.toCStorageRef.key
  | .divisionOutput => refs.division.output.toCStorageRef.key
  | .reduceProduct => refs.reduceProduct.toCStorageRef.key

/-- All named third-phase cells have pairwise distinct storage identities. -/
structure PhaseSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  keyInjective : Function.Injective (phaseCellKey refs)

/-- Different named third-phase cells resolve to different storage keys. -/
lemma PhaseSeparation.phaseCellKey_ne {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} {refs : Refs ctx width} (separation : PhaseSeparation refs)
    (left right : PhaseCell) (different : left ≠ right) :
    phaseCellKey refs left ≠ phaseCellKey refs right := by
  intro equal
  exact different (separation.keyInjective equal)

/-- Complete per-phase separation for one third-coordinate transition. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  phase : PhaseSeparation refs
  cross : LatticeCross.PointCrossSeparation refs.basis.first refs.basis.second refs.cross
    refs.productLeft refs.productRight
  numeratorDot : LatticeDotRefresh.Separation refs.target refs.cross (numeratorDotRefs refs)
  denominatorDot : LatticeDotRefresh.Separation refs.basis.third refs.cross
    (denominatorDotRefs refs)
  division : SignedWord.RoundedDiv.Separation refs.division
  reduction : LatticeArithmetic.PointReduceSeparation
    (SignedWord.writeInput refs.division.output) refs.basis.third refs.target
      refs.reduceProduct

/-- The integer cross product used by the third-coordinate numerator and denominator. -/
def crossValue (firstValue secondValue : NumberTheory.IntegerPoint3) :
    NumberTheory.IntegerPoint3 :=
  NumberTheory.integerPointCross firstValue secondValue

/-- The target-to-cross dot product used as the third-coordinate numerator. -/
def numeratorValue (firstValue secondValue targetValue : NumberTheory.IntegerPoint3) : Int :=
  NumberTheory.integerPointDot targetValue (crossValue firstValue secondValue)

/-- The third-row-to-cross dot product used as the signed denominator. -/
def denominatorValue (firstValue secondValue thirdValue : NumberTheory.IntegerPoint3) : Int :=
  NumberTheory.integerPointDot thirdValue (crossValue firstValue secondValue)

/-- Exactly the numeric conditions required by signed denominator normalization and division. -/
structure NormalizeFits (width : Nat) (numerator denominator : Int) : Prop where
  widthPositive : 0 < width
  numeratorFits :
    ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable width
      (if denominator < 0 then -numerator else numerator)
  denominatorNonzero : denominator ≠ 0
  denominatorMagnitudeFits : denominator.natAbs < CShape.wordModulus width
  denominatorSignedFits :
    ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable width denominator

/-- The original third-coordinate integer domain with arbitrary initial scratch. -/
abbrev Fits (width : Nat)
    (firstValue secondValue thirdValue targetValue : NumberTheory.IntegerPoint3) : Prop :=
  NormalizeFits width (numeratorValue firstValue secondValue targetValue)
    (denominatorValue firstValue secondValue thirdValue)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird
