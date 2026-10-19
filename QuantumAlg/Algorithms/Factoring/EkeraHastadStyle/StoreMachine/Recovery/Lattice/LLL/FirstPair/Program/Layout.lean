/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Correctness
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Gram.Norm
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FirstPair.Lovasz
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Row.Swap.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Row.Swap.Resources

/-!
# Actual first-pair LLL layout and original numeric domain

The original references and phase-local separation support actual division,
row reduction, norm refresh, Lovasz decision and the selected row exchange.
Only the actual numerator and denominator readings are required initially;
other Gram or scratch words need no initial-value certificate.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFirstPairMachine

open ClassicalRoutines.NumberTheory
open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

/-- All caller-owned cells for one first-pair transition after a Gram snapshot. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Nested references for the basis stage. -/
  basis : LatticeState.BasisRefs ctx width
  /-- Nested references for the metric stage. -/
  metric : LatticeMetricMachine.Refs ctx width
  /-- Nested references for the division stage. -/
  division : SignedWord.RoundedDiv.BodyRefs ctx width
  /-- Writable cell for the reduce product value. -/
  reduceProduct : CWriteRef ctx (.unsignedWord width)
  reduceProductRole : reduceProduct.toCStorageRef.role = .workspace
  /-- Nested references for the refresh stage. -/
  refresh : LatticeNormRefresh.Refs ctx width
  /-- Nested references for the lovasz stage. -/
  lovasz : LatticeLovasz.FirstLovaszRefs ctx
  /-- Writable cell for the swap scratch value. -/
  swapScratch : CWriteRef ctx (.unsignedWord width)
  swapScratchRole : swapScratch.toCStorageRef.role = .workspace
  numerator : division.numerator = SignedWord.writeInput metric.g21
  denominator : division.denominator = SignedWord.writeInput metric.g11
  refreshNorm : refresh.norm = metric.g22

/-- Every independently writable cell touched by one first-pair transition. -/
inductive TransitionCell where
  | b11 | b12 | b13 | b21 | b22 | b23 | b31 | b32 | b33
  | g11 | g21 | g31 | g22 | g32 | g33 | metricProduct
  | magnitude | negative | wideNumerator | wideDenominator | division | coefficient
  | reduceProduct | refreshProduct | passes | swapScratch
deriving DecidableEq

/-- Resolve each transition cell to its concrete caller-owned storage key. -/
def cellKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : TransitionCell → StorageKey
  | .b11 => refs.basis.first.first.toCStorageRef.key
  | .b12 => refs.basis.first.second.toCStorageRef.key
  | .b13 => refs.basis.first.third.toCStorageRef.key
  | .b21 => refs.basis.second.first.toCStorageRef.key
  | .b22 => refs.basis.second.second.toCStorageRef.key
  | .b23 => refs.basis.second.third.toCStorageRef.key
  | .b31 => refs.basis.third.first.toCStorageRef.key
  | .b32 => refs.basis.third.second.toCStorageRef.key
  | .b33 => refs.basis.third.third.toCStorageRef.key
  | .g11 => refs.metric.g11.toCStorageRef.key
  | .g21 => refs.metric.g21.toCStorageRef.key
  | .g31 => refs.metric.g31.toCStorageRef.key
  | .g22 => refs.metric.g22.toCStorageRef.key
  | .g32 => refs.metric.g32.toCStorageRef.key
  | .g33 => refs.metric.g33.toCStorageRef.key
  | .metricProduct => refs.metric.product.toCStorageRef.key
  | .magnitude => refs.division.magnitude.toCStorageRef.key
  | .negative => refs.division.negative.toCStorageRef.key
  | .wideNumerator => refs.division.wideNumerator.toCStorageRef.key
  | .wideDenominator => refs.division.wideDenominator.toCStorageRef.key
  | .division => refs.division.division.toCStorageRef.key
  | .coefficient => refs.division.output.toCStorageRef.key
  | .reduceProduct => refs.reduceProduct.toCStorageRef.key
  | .refreshProduct => refs.refresh.product.toCStorageRef.key
  | .passes => refs.lovasz.passes.toCStorageRef.key
  | .swapScratch => refs.swapScratch.toCStorageRef.key

/-- Embed one named basis coordinate into the transition-wide cell naming. -/
def basisTransitionCell : LatticeMetricMachine.BasisCell → TransitionCell
  | .firstFirst => .b11
  | .firstSecond => .b12
  | .firstThird => .b13
  | .secondFirst => .b21
  | .secondSecond => .b22
  | .secondThird => .b23
  | .thirdFirst => .b31
  | .thirdSecond => .b32
  | .thirdThird => .b33

/-- Embed one named Gram cell into the transition-wide cell naming. -/
def metricTransitionCell : LatticeMetricMachine.MetricCell → TransitionCell
  | .g11 => .g11
  | .g21 => .g21
  | .g31 => .g31
  | .g22 => .g22
  | .g32 => .g32
  | .g33 => .g33
  | .product => .metricProduct

/-- All transition cells have pairwise distinct storage keys. -/
structure PhaseSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  keyInjective : Function.Injective (cellKey refs)

/-- Different named transition cells resolve to different storage keys. -/
lemma PhaseSeparation.cellKey_ne {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} {refs : Refs ctx width} (separation : PhaseSeparation refs)
    (left right : TransitionCell) (different : left ≠ right) :
    cellKey refs left ≠ cellKey refs right := by
  intro equal
  exact different (separation.keyInjective equal)

/-- Per-phase separation supplied by the caller. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  phase : PhaseSeparation refs
  division : SignedWord.RoundedDiv.Separation refs.division
  reduction : LatticeArithmetic.PointReduceSeparation
    (SignedWord.writeInput refs.division.output) refs.basis.first refs.basis.second
      refs.reduceProduct
  refresh : LatticeNormRefresh.Separation refs.basis.second refs.refresh
  lovasz : LatticeLovasz.FirstLovaszSeparation refs.metric refs.lovasz
  swap : LatticeSwap.PointSwapSeparation refs.basis.first refs.basis.second refs.swapScratch

/-- The original pure basis selected after the first Lovasz decision. -/
def lovaszBranchResult (reduced : NumberTheory.IntegerBasis3) : NumberTheory.IntegerBasis3 :=
  if reduced.firstLovasz then reduced else reduced.swapFirstSecond

/-- Original first-pair size reduction followed by its original Lovasz choice. -/
def firstPairResult (basis : NumberTheory.IntegerBasis3) : NumberTheory.IntegerBasis3 :=
  lovaszBranchResult basis.sizeReduceFirstPair.1

/-- Original source representation and actual division input readings. -/
structure Initial {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) (store : Store ctx) (basis : NumberTheory.IntegerBasis3) : Prop where
  basisRep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis
  numerator : decodeRawSignedWord (store.read refs.division.numerator) =
    NumberTheory.integerPointDot basis.second basis.first
  denominator : (store.read refs.division.denominator).toNat =
    NumberTheory.integerPointSquaredNorm basis.first

/-- The original width, nonzero denominator and Lovasz capacity conditions. -/
structure Fits (width : Nat) (basis : NumberTheory.IntegerBasis3) : Prop where
  widthPositive : 0 < width
  denominatorPositive : 0 < NumberTheory.integerPointSquaredNorm basis.first
  firstFits : NumberTheory.integerPointSquaredNorm basis.first < CShape.wordModulus width
  twiceSecondFits : 2 * NumberTheory.integerPointSquaredNorm basis.sizeReduceFirstPair.1.second <
    CShape.wordModulus width

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFirstPairMachine
