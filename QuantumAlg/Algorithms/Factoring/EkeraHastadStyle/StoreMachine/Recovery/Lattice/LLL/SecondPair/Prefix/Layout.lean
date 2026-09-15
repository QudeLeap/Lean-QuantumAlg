/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Inputs.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Inputs.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Gram.Program.Layout
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Correctness
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Resources
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Restoration

/-!
# Original second-pair prefix layout and domain

The original basis, selected Gram entries, scratch and two division packages
retain their identities. Only the Gram entries not refreshed by this prefix
need an initial representation premise.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairMachine

open ClassicalRoutines.NumberTheory
open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

/-- All caller-owned cells needed by the second-pair transition. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Nested references for the basis stage. -/
  basis : LatticeState.BasisRefs ctx width
  /-- Nested references for the metric stage. -/
  metric : LatticeMetricMachine.Refs ctx width
  /-- Writable cell for the refresh g 21 product value. -/
  refreshG21Product : CWriteRef ctx (.unsignedWord width)
  refreshG21ProductRole : refreshG21Product.toCStorageRef.role = .workspace
  /-- Writable cell for the refresh g 32 product value. -/
  refreshG32Product : CWriteRef ctx (.unsignedWord width)
  refreshG32ProductRole : refreshG32Product.toCStorageRef.role = .workspace
  /-- Nested references for the reduction inputs stage. -/
  reductionInputs : LatticeSecondReductionInputs.Refs ctx width
  /-- Nested references for the division 32 stage. -/
  division32 : SignedWord.RoundedDiv.BodyRefs ctx width
  /-- Nested references for the division 31 stage. -/
  division31 : SignedWord.RoundedDiv.BodyRefs ctx width
  /-- Writable cell for the reduce product value. -/
  reduceProduct : CWriteRef ctx (.unsignedWord width)
  reduceProductRole : reduceProduct.toCStorageRef.role = .workspace
  division32Numerator : division32.numerator = SignedWord.writeInput reductionInputs.nu32
  division32Denominator : division32.denominator = SignedWord.writeInput reductionInputs.d32

/-- The refresh package whose accumulator is the live `g21` metric word. -/
abbrev refreshG21Refs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : LatticeDotRefresh.Refs ctx width where
  dot := refs.metric.g21
  dotRole := refs.metric.g21Role
  product := refs.refreshG21Product
  productRole := refs.refreshG21ProductRole

/-- The refresh package whose accumulator is the live `g32` metric word. -/
abbrev refreshG32Refs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : LatticeDotRefresh.Refs ctx width where
  dot := refs.metric.g32
  dotRole := refs.metric.g32Role
  product := refs.refreshG32Product
  productRole := refs.refreshG32ProductRole

/-- The five structural metric reads used to derive the `mu32` division inputs. -/
abbrev reductionInputs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : LatticeSecondReductionInputs.Inputs ctx width where
  g11 := SignedWord.writeInput refs.metric.g11
  g21 := SignedWord.writeInput refs.metric.g21
  g31 := SignedWord.writeInput refs.metric.g31
  g22 := SignedWord.writeInput refs.metric.g22
  g32 := SignedWord.writeInput refs.metric.g32

/-- Names of every mutable word allocated by either rounded-division body. -/
inductive DivisionCell where
  | magnitude | negative | wideNumerator | wideDenominator | division | output
deriving DecidableEq

/-- Canonical writable cells for the whole second-pair machine allocation. -/
inductive TransitionCell where
  | b11 | b12 | b13 | b21 | b22 | b23 | b31 | b32 | b33
  | g11 | g21 | g31 | g22 | g32 | g33 | metricProduct
  | refreshG21Product | refreshG32Product
  | nu32 | d32 | reductionInputsProduct
  | division32 (cell : DivisionCell)
  | division31 (cell : DivisionCell)
  | reduceProduct
deriving DecidableEq

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

/-- Resolve each canonical writable cell to its caller-owned storage key. -/
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
  | .refreshG21Product => refs.refreshG21Product.toCStorageRef.key
  | .refreshG32Product => refs.refreshG32Product.toCStorageRef.key
  | .nu32 => refs.reductionInputs.nu32.toCStorageRef.key
  | .d32 => refs.reductionInputs.d32.toCStorageRef.key
  | .reductionInputsProduct => refs.reductionInputs.product.toCStorageRef.key
  | .division32 .magnitude => refs.division32.magnitude.toCStorageRef.key
  | .division32 .negative => refs.division32.negative.toCStorageRef.key
  | .division32 .wideNumerator => refs.division32.wideNumerator.toCStorageRef.key
  | .division32 .wideDenominator => refs.division32.wideDenominator.toCStorageRef.key
  | .division32 .division => refs.division32.division.toCStorageRef.key
  | .division32 .output => refs.division32.output.toCStorageRef.key
  | .division31 .magnitude => refs.division31.magnitude.toCStorageRef.key
  | .division31 .negative => refs.division31.negative.toCStorageRef.key
  | .division31 .wideNumerator => refs.division31.wideNumerator.toCStorageRef.key
  | .division31 .wideDenominator => refs.division31.wideDenominator.toCStorageRef.key
  | .division31 .division => refs.division31.division.toCStorageRef.key
  | .division31 .output => refs.division31.output.toCStorageRef.key
  | .reduceProduct => refs.reduceProduct.toCStorageRef.key

/-- Embed one named Gram cell into the transition-wide cell naming. -/
def metricTransitionCell : LatticeMetricMachine.MetricCell → TransitionCell
  | .g11 => .g11
  | .g21 => .g21
  | .g31 => .g31
  | .g22 => .g22
  | .g32 => .g32
  | .g33 => .g33
  | .product => .metricProduct

/-- Global key separation, including the two independent rounded-division bodies. -/
structure PhaseSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  keyInjective : Function.Injective (cellKey refs)

/-- Different named transition cells have different concrete storage keys. -/
theorem PhaseSeparation.cellKey_ne {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} {refs : Refs ctx width} (separation : PhaseSeparation refs)
    (left right : TransitionCell) (different : left ≠ right) :
    cellKey refs left ≠ cellKey refs right := by
  intro equal
  exact different (separation.keyInjective equal)

/-- Local source-to-write separation supplied for each literal prefix phase. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  phase : PhaseSeparation refs
  refreshG21 : LatticeDotRefresh.Separation refs.basis.second refs.basis.first
    (refreshG21Refs refs)
  refreshG32 : LatticeDotRefresh.Separation refs.basis.third refs.basis.second
    (refreshG32Refs refs)
  inputs : LatticeSecondReductionInputs.Separation (reductionInputs refs) refs.reductionInputs
  division32 : SignedWord.RoundedDiv.Separation refs.division32
  division31 : SignedWord.RoundedDiv.Separation refs.division31
  reduction : LatticeArithmetic.PointReduceSeparation
    (SignedWord.writeInput refs.division32.output) refs.basis.second refs.basis.third
      refs.reduceProduct

/-- Original pure third-row reduction against the second row. -/
def secondPairPrefixResult (basis : NumberTheory.IntegerBasis3) : NumberTheory.IntegerBasis3 :=
  basis.reduceThirdBySecond basis.sizeReduceSecondPair.2.1

/-- The original actual basis and precisely the three metric words not refreshed here. -/
structure Initial {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) (store : Store ctx) (basis : NumberTheory.IntegerBasis3) : Prop where
  basisRep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis
  firstNorm : RawSignedRepresents (store.read (writeInput refs.metric.g11))
    (NumberTheory.integerPointSquaredNorm basis.first : Int)
  thirdFirstDot : RawSignedRepresents (store.read (writeInput refs.metric.g31))
    (NumberTheory.integerPointDot basis.third basis.first)
  secondNorm : RawSignedRepresents (store.read (writeInput refs.metric.g22))
    (NumberTheory.integerPointSquaredNorm basis.second : Int)

/-- Exactly the original signed numerator and positive denominator capacity conditions. -/
structure Fits (width : Nat) (basis : NumberTheory.IntegerBasis3) : Prop where
  widthPositive : 0 < width
  numeratorFits : ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable width
    basis.secondReductionNumerator
  denominatorPositive : 0 < basis.secondReductionDenominator
  denominatorFits : basis.secondReductionDenominator < CShape.wordModulus width

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairMachine
