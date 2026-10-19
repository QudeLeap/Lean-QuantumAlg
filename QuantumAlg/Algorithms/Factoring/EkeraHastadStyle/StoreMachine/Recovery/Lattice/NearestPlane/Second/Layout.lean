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
# Actual second-coordinate nearest-plane layout

The existing mathematical domain and named caller cells are retained. Separation
refers to the actual storage keys used by the native instructions.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond

open ClassicalAlgorithms.NumberTheory
open ClassicalRoutines.NumberTheory
open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

/-- Caller-owned cells for one raw nearest-plane second-coordinate reduction. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Nested references for the basis stage. -/
  basis : LatticeState.BasisRefs ctx width
  /-- Nested references for the target stage. -/
  target : LatticeState.PointRefs ctx width
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

/-- Dot-refresh view for the first-row squared norm. -/
def g11DotRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : LatticeDotRefresh.Refs ctx width where
  dot := refs.g11
  dotRole := refs.g11Role
  product := refs.dotProduct
  productRole := refs.dotProductRole

/-- Dot-refresh view for the second-first Gram entry. -/
def g21DotRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : LatticeDotRefresh.Refs ctx width where
  dot := refs.g21
  dotRole := refs.g21Role
  product := refs.dotProduct
  productRole := refs.dotProductRole

/-- Dot-refresh view for the residual target against the second row. -/
def targetSecondDotRefs {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (refs : Refs ctx width) : LatticeDotRefresh.Refs ctx width where
  dot := refs.targetDotSecond
  dotRole := refs.targetDotSecondRole
  product := refs.dotProduct
  productRole := refs.dotProductRole

/-- Dot-refresh view for the residual target against the first row. -/
def targetFirstDotRefs {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (refs : Refs ctx width) : LatticeDotRefresh.Refs ctx width where
  dot := refs.targetDotFirst
  dotRole := refs.targetDotFirstRole
  product := refs.dotProduct
  productRole := refs.dotProductRole

/-- Dot-refresh view for the squared norm of the first-two-row cross product. -/
def denominatorDotRefs {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (refs : Refs ctx width) : LatticeDotRefresh.Refs ctx width where
  dot := refs.denominator
  dotRole := refs.denominatorRole
  product := refs.dotProduct
  productRole := refs.dotProductRole

/-- Named cells whose pairwise separation supports the complete second phase. -/
inductive PhaseCell where
  | basisFirstFirst | basisFirstSecond | basisFirstThird
  | basisSecondFirst | basisSecondSecond | basisSecondThird
  | targetFirst | targetSecond | targetThird
  | crossFirst | crossSecond | crossThird
  | crossProductLeft | crossProductRight | dotProduct
  | g11 | g21 | targetDotSecond | targetDotFirst | numerator | numeratorProduct | denominator
  | divisionMagnitude | divisionNegative | divisionWideNumerator
  | divisionWideDenominator | divisionQuotientRemainder | divisionOutput
  | reduceProduct
deriving DecidableEq

/-- Resolve one named second-phase cell to its caller-owned storage key. -/
def phaseCellKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : PhaseCell → StorageKey
  | .basisFirstFirst => refs.basis.first.first.toCStorageRef.key
  | .basisFirstSecond => refs.basis.first.second.toCStorageRef.key
  | .basisFirstThird => refs.basis.first.third.toCStorageRef.key
  | .basisSecondFirst => refs.basis.second.first.toCStorageRef.key
  | .basisSecondSecond => refs.basis.second.second.toCStorageRef.key
  | .basisSecondThird => refs.basis.second.third.toCStorageRef.key
  | .targetFirst => refs.target.first.toCStorageRef.key
  | .targetSecond => refs.target.second.toCStorageRef.key
  | .targetThird => refs.target.third.toCStorageRef.key
  | .crossFirst => refs.cross.first.toCStorageRef.key
  | .crossSecond => refs.cross.second.toCStorageRef.key
  | .crossThird => refs.cross.third.toCStorageRef.key
  | .crossProductLeft => refs.crossProductLeft.toCStorageRef.key
  | .crossProductRight => refs.crossProductRight.toCStorageRef.key
  | .dotProduct => refs.dotProduct.toCStorageRef.key
  | .g11 => refs.g11.toCStorageRef.key
  | .g21 => refs.g21.toCStorageRef.key
  | .targetDotSecond => refs.targetDotSecond.toCStorageRef.key
  | .targetDotFirst => refs.targetDotFirst.toCStorageRef.key
  | .numerator => refs.numerator.toCStorageRef.key
  | .numeratorProduct => refs.numeratorProduct.toCStorageRef.key
  | .denominator => refs.denominator.toCStorageRef.key
  | .divisionMagnitude => refs.division.magnitude.toCStorageRef.key
  | .divisionNegative => refs.division.negative.toCStorageRef.key
  | .divisionWideNumerator => refs.division.wideNumerator.toCStorageRef.key
  | .divisionWideDenominator => refs.division.wideDenominator.toCStorageRef.key
  | .divisionQuotientRemainder => refs.division.division.toCStorageRef.key
  | .divisionOutput => refs.division.output.toCStorageRef.key
  | .reduceProduct => refs.reduceProduct.toCStorageRef.key

/-- All named second-phase cells have pairwise distinct storage identities. -/
structure PhaseSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  keyInjective : Function.Injective (phaseCellKey refs)

/-- Different named second-phase cells resolve to different storage keys. -/
lemma PhaseSeparation.phaseCellKey_ne {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} {refs : Refs ctx width} (separation : PhaseSeparation refs)
    (left right : PhaseCell) (different : left ≠ right) :
    phaseCellKey refs left ≠ phaseCellKey refs right := by
  intro equal
  exact different (separation.keyInjective equal)

/-- Numeric hypotheses needed by exact rounded division at the common width. -/
structure Fits (width : Nat) (basis : NumberTheory.IntegerBasis3)
    (target : NumberTheory.IntegerPoint3) : Prop where
  widthPositive : 0 < width
  numeratorRange :
    XGCD.signedRepresentable width
      (LatticeNearestPlaneResidual.secondNumerator basis
        (LatticeNearestPlaneResidual.afterThird basis target))
  denominatorPositive : 0 < basis.secondReductionDenominator
  denominatorFits :
    basis.secondReductionDenominator.natAbs < CShape.wordModulus width

/-- Standalone input representation for the second residual stage. -/
def Initial {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (before : Store ctx) (refs : Refs ctx width)
    (basis : NumberTheory.IntegerBasis3)
    (target : NumberTheory.IntegerPoint3) : Prop :=
  LatticeArithmetic.PointRawRepresents before refs.basis.first basis.first ∧
    LatticeArithmetic.PointRawRepresents before refs.basis.second basis.second ∧
      LatticeArithmetic.PointRawRepresents before refs.target
        (LatticeNearestPlaneResidual.afterThird basis target)

/-- Phase-local separation certificates for the actual second circuit. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  phase : PhaseSeparation refs
  cross : LatticeCross.PointCrossSeparation refs.basis.first refs.basis.second refs.cross
    refs.crossProductLeft refs.crossProductRight
  g11Dot : LatticeDotRefresh.Separation refs.basis.first refs.basis.first
    (g11DotRefs refs)
  g21Dot : LatticeDotRefresh.Separation refs.basis.second refs.basis.first
    (g21DotRefs refs)
  targetSecondDot : LatticeDotRefresh.Separation refs.target refs.basis.second
    (targetSecondDotRefs refs)
  targetFirstDot : LatticeDotRefresh.Separation refs.target refs.basis.first
    (targetFirstDotRefs refs)
  denominatorDot : LatticeDotRefresh.Separation refs.cross refs.cross
    (denominatorDotRefs refs)
  division : SignedWord.RoundedDiv.Separation refs.division
  reduction : LatticeArithmetic.PointReduceSeparation
    (SignedWord.writeInput refs.division.output) refs.basis.second refs.target
      refs.reduceProduct

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond
