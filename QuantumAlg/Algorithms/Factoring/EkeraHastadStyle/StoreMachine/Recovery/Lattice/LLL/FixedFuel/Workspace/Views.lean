/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Workspace.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.State.Workspace.Views

/-!
# Fixed-fuel LLL scratch component views

This module maps the reusable 42-cell inventory into the Gram snapshot, both
LLL phase packages, and the fixed-fuel driver.  The first phase reuses one
rounded-division body and compatible second-phase scratch cells because the two
branches are mutually exclusive.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeFixedFuelScratchWorkspaceViews

open ClassicalRoutines
open ClassicalRoutines.NumberTheory
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

namespace Scratch

/-- Abbreviation for the local cell interface. -/
abbrev Cell := LatticeFixedFuelScratchWorkspaceLayout.Cell

/-- Abbreviation for the local width interface. -/
abbrev Width (N : Nat) := LatticeFixedFuelScratchWorkspaceLayout.Width N

/-- Abbreviation for the local cells interface. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N

/-- Abbreviation for the local cell ref interface. -/
abbrev cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) :=
  LatticeFixedFuelScratchWorkspaceLayout.cellRef cells cell

end Scratch

namespace State

/-- Abbreviation for the local cells interface. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  LatticePairStateWorkspaceViews.Layout.Cells ctx N

end State

/-- Seven-cell shared Gram snapshot view. -/
def metricRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) :
    LatticeMetricMachine.Refs ctx (Scratch.Width N) where
  g11 := Scratch.cellRef scratch .metricG11
  g11Role := LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .metricG11
  g21 := Scratch.cellRef scratch .metricG21
  g21Role := LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .metricG21
  g31 := Scratch.cellRef scratch .metricG31
  g31Role := LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .metricG31
  g22 := Scratch.cellRef scratch .metricG22
  g22Role := LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .metricG22
  g32 := Scratch.cellRef scratch .metricG32
  g32Role := LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .metricG32
  g33 := Scratch.cellRef scratch .metricG33
  g33Role := LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .metricG33
  product := Scratch.cellRef scratch .metricProduct
  productRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .metricProduct

/-- Rounded division reused by the first-pair branch. -/
def firstDivisionRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) :
    RoundedDiv.BodyRefs ctx (Scratch.Width N) where
  numerator := SignedWord.writeInput (metricRefs scratch).g21
  denominator := SignedWord.writeInput (metricRefs scratch).g11
  output := Scratch.cellRef scratch .division32Output
  magnitude := Scratch.cellRef scratch .division32Magnitude
  negative := Scratch.cellRef scratch .division32Negative
  wideNumerator := Scratch.cellRef scratch .division32WideNumerator
  wideDenominator := Scratch.cellRef scratch .division32WideDenominator
  division := Scratch.cellRef scratch .division32Division
  magnitudeRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .division32Magnitude
  negativeRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .division32Negative
  wideNumeratorRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch
      .division32WideNumerator
  wideDenominatorRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch
      .division32WideDenominator
  divisionRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .division32Division
  outputWritable := Or.inl
    (LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .division32Output)

/-- First-pair norm refresh, reusing one second-prefix product cell. -/
def firstRefreshRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) :
    LatticeNormRefresh.Refs ctx (Scratch.Width N) where
  norm := (metricRefs scratch).g22
  normRole := (metricRefs scratch).g22Role
  product := Scratch.cellRef scratch .refreshG21Product
  productRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .refreshG21Product

/-- First-pair Lovasz decision bit, shared with the second branch. -/
def firstLovaszRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) : LatticeLovasz.FirstLovaszRefs ctx where
  passes := Scratch.cellRef scratch .lovaszPasses
  passesRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .lovaszPasses

/-- Complete first-pair branch over the shared physical cells. -/
def firstRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : State.Cells ctx N) (scratch : Scratch.Cells ctx N) :
    LatticeFirstPairMachine.Refs ctx (Scratch.Width N) where
  basis := LatticePairStateWorkspaceViews.basisRefs state
  metric := metricRefs scratch
  division := firstDivisionRefs scratch
  reduceProduct := Scratch.cellRef scratch .reduceProduct
  reduceProductRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .reduceProduct
  refresh := firstRefreshRefs scratch
  lovasz := firstLovaszRefs scratch
  swapScratch := Scratch.cellRef scratch .swapScratch
  swapScratchRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .swapScratch
  numerator := rfl
  denominator := rfl
  refreshNorm := rfl

/-- Three mutable inputs used to derive the second rounded coefficient. -/
def reductionInputRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) :
    LatticeSecondReductionInputs.Refs ctx (Scratch.Width N) where
  nu32 := Scratch.cellRef scratch .nu32
  nu32Role := LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .nu32
  d32 := Scratch.cellRef scratch .d32
  d32Role := LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .d32
  product := Scratch.cellRef scratch .reductionInputsProduct
  productRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .reductionInputsProduct

/-- Rounded division for the second-direction coefficient. -/
def division32Refs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) :
    RoundedDiv.BodyRefs ctx (Scratch.Width N) where
  numerator := SignedWord.writeInput (reductionInputRefs scratch).nu32
  denominator := SignedWord.writeInput (reductionInputRefs scratch).d32
  output := Scratch.cellRef scratch .division32Output
  magnitude := Scratch.cellRef scratch .division32Magnitude
  negative := Scratch.cellRef scratch .division32Negative
  wideNumerator := Scratch.cellRef scratch .division32WideNumerator
  wideDenominator := Scratch.cellRef scratch .division32WideDenominator
  division := Scratch.cellRef scratch .division32Division
  magnitudeRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .division32Magnitude
  negativeRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .division32Negative
  wideNumeratorRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch
      .division32WideNumerator
  wideDenominatorRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch
      .division32WideDenominator
  divisionRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .division32Division
  outputWritable := Or.inl
    (LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .division32Output)

/-- Rounded division for the final first-direction coefficient. -/
def division31Refs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) :
    RoundedDiv.BodyRefs ctx (Scratch.Width N) where
  numerator := SignedWord.writeInput (metricRefs scratch).g31
  denominator := SignedWord.writeInput (metricRefs scratch).g11
  output := Scratch.cellRef scratch .division31Output
  magnitude := Scratch.cellRef scratch .division31Magnitude
  negative := Scratch.cellRef scratch .division31Negative
  wideNumerator := Scratch.cellRef scratch .division31WideNumerator
  wideDenominator := Scratch.cellRef scratch .division31WideDenominator
  division := Scratch.cellRef scratch .division31Division
  magnitudeRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .division31Magnitude
  negativeRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .division31Negative
  wideNumeratorRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch
      .division31WideNumerator
  wideDenominatorRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch
      .division31WideDenominator
  divisionRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .division31Division
  outputWritable := Or.inl
    (LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .division31Output)

/-- Prefix package of the complete second-pair branch. -/
def secondMachineRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : State.Cells ctx N) (scratch : Scratch.Cells ctx N) :
    LatticeSecondPairMachine.Refs ctx (Scratch.Width N) where
  basis := LatticePairStateWorkspaceViews.basisRefs state
  metric := metricRefs scratch
  refreshG21Product := Scratch.cellRef scratch .refreshG21Product
  refreshG21ProductRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .refreshG21Product
  refreshG32Product := Scratch.cellRef scratch .refreshG32Product
  refreshG32ProductRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .refreshG32Product
  reductionInputs := reductionInputRefs scratch
  division32 := division32Refs scratch
  division31 := division31Refs scratch
  reduceProduct := Scratch.cellRef scratch .reduceProduct
  reduceProductRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .reduceProduct
  division32Numerator := rfl
  division32Denominator := rfl

/-- Post-reduction view of the same second-pair prefix cells. -/
def secondPostRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : State.Cells ctx N) (scratch : Scratch.Cells ctx N) :
    LatticeSecondPairPostReduction.Refs ctx (Scratch.Width N) where
  machine := secondMachineRefs state scratch
  numerator := rfl
  denominator := rfl

/-- First--second squared-area refresh package. -/
def area12Refs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) :
    LatticeAreaRefresh.Refs ctx (Scratch.Width N) where
  cross := {
    first := Scratch.cellRef scratch .area12CrossFirst
    firstRole :=
      LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .area12CrossFirst
    second := Scratch.cellRef scratch .area12CrossSecond
    secondRole :=
      LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .area12CrossSecond
    third := Scratch.cellRef scratch .area12CrossThird
    thirdRole :=
      LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .area12CrossThird }
  productLeft := Scratch.cellRef scratch .area12ProductLeft
  productLeftRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .area12ProductLeft
  productRight := Scratch.cellRef scratch .area12ProductRight
  productRightRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .area12ProductRight
  area := Scratch.cellRef scratch .area12Result
  areaRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .area12Result
  normProduct := Scratch.cellRef scratch .area12NormProduct
  normProductRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .area12NormProduct

/-- First--third squared-area refresh package. -/
def area13Refs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) :
    LatticeAreaRefresh.Refs ctx (Scratch.Width N) where
  cross := {
    first := Scratch.cellRef scratch .area13CrossFirst
    firstRole :=
      LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .area13CrossFirst
    second := Scratch.cellRef scratch .area13CrossSecond
    secondRole :=
      LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .area13CrossSecond
    third := Scratch.cellRef scratch .area13CrossThird
    thirdRole :=
      LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .area13CrossThird }
  productLeft := Scratch.cellRef scratch .area13ProductLeft
  productLeftRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .area13ProductLeft
  productRight := Scratch.cellRef scratch .area13ProductRight
  productRightRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .area13ProductRight
  area := Scratch.cellRef scratch .area13Result
  areaRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .area13Result
  normProduct := Scratch.cellRef scratch .area13NormProduct
  normProductRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .area13NormProduct

/-- Second Lovasz arithmetic over the two live squared-area words. -/
def secondLovaszRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) :
    LatticeLovasz.SecondLovaszRefs ctx (Scratch.Width N) where
  area12 := SignedWord.writeInput (area12Refs scratch).area
  area13 := SignedWord.writeInput (area13Refs scratch).area
  doubled := Scratch.cellRef scratch .lovaszDoubled
  doubledRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .lovaszDoubled
  passes := Scratch.cellRef scratch .lovaszPasses
  passesRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .lovaszPasses

/-- Final decision and swap package of the second branch. -/
def secondBranchRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : State.Cells ctx N) (scratch : Scratch.Cells ctx N) :
    LatticeSecondLovaszBranch.Refs ctx (Scratch.Width N) where
  basis := LatticePairStateWorkspaceViews.basisRefs state
  lovasz := secondLovaszRefs scratch
  swapScratch := Scratch.cellRef scratch .swapScratch
  swapScratchRole :=
    LatticeFixedFuelScratchWorkspaceLayout.cellRef_role scratch .swapScratch

/-- Complete second-pair branch over its maximum live scratch footprint. -/
def secondRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : State.Cells ctx N) (scratch : Scratch.Cells ctx N) :
    LatticeSecondPairFullMachine.Refs ctx (Scratch.Width N) where
  machine := secondMachineRefs state scratch
  post := secondPostRefs state scratch
  area12 := area12Refs scratch
  area13 := area13Refs scratch
  branch := secondBranchRefs state scratch
  postMachine := rfl
  branchBasis := rfl
  branchArea12 := rfl
  branchArea13 := rfl

/-- Complete fixed-fuel driver sharing the persistent basis and phase latches. -/
def driverRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : State.Cells ctx N) (scratch : Scratch.Cells ctx N) :
    LatticeFixedFuelMachine.Refs ctx (Scratch.Width N) where
  machine := LatticePairStateWorkspaceViews.machineRefs state
  metric := metricRefs scratch
  first := firstRefs state scratch
  second := secondRefs state scratch
  firstBasis := rfl
  firstMetric := rfl
  secondBasis := rfl
  secondMetric := rfl

/-- Initialization package over one decoded pair and the physical driver view. -/
def initializationRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : State.Cells ctx N) (scratch : Scratch.Cells ctx N)
    (pair : BatchMachine.PairRefs ctx N) :
    LatticeFixedFuelInitializationMachine.Refs ctx N where
  pair := pair
  raw := LatticePairStateWorkspaceViews.rawRefs state
  roles := LatticePairStateWorkspaceViews.rawRoles state
  driver := driverRefs state scratch
  basisWiring := rfl

end

end LatticeFixedFuelScratchWorkspaceViews
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
