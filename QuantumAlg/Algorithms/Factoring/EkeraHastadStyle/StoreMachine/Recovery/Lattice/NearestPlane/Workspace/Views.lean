/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Workspace.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Input.Workspace.Views
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.NearestPlane.Program

/-!
# Three-stage nearest-plane scratch component views

This module maps the reusable 21-cell package into the third-, second-, and
first-coordinate routines.  The three quotient outputs occupy distinct cells
after the full sequence even though the remaining phase-local scratch is
reused.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeNearestPlaneScratchWorkspaceViews

open ClassicalRoutines
open ClassicalRoutines.NumberTheory
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

namespace Scratch

/-- Abbreviation for the local cell interface. -/
abbrev Cell := LatticeNearestPlaneScratchWorkspaceLayout.Cell

/-- Abbreviation for the local width interface. -/
abbrev Width (N : Nat) := LatticeNearestPlaneScratchWorkspaceLayout.Width N

/-- Abbreviation for the local cells interface. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N

/-- Abbreviation for the local cell ref interface. -/
abbrev cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) :=
  LatticeNearestPlaneScratchWorkspaceLayout.cellRef cells cell

end Scratch

namespace State

/-- Abbreviation for the local cells interface. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  LatticePairStateWorkspaceViews.Layout.Cells ctx N

end State

/-- Shared cross-product point reused by the third and second phases. -/
def crossRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) :
    LatticeState.PointRefs ctx (Scratch.Width N) where
  first := Scratch.cellRef scratch .crossFirst
  firstRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .crossFirst
  second := Scratch.cellRef scratch .crossSecond
  secondRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .crossSecond
  third := Scratch.cellRef scratch .crossThird
  thirdRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .crossThird

/-- Rounded-division body whose quotient persists as the third coefficient. -/
def thirdDivisionRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) :
    RoundedDiv.BodyRefs ctx (Scratch.Width N) where
  numerator := SignedWord.writeInput (Scratch.cellRef scratch .numerator)
  denominator := SignedWord.writeInput (Scratch.cellRef scratch .g11)
  output := Scratch.cellRef scratch .thirdOutput
  magnitude := Scratch.cellRef scratch .divisionMagnitude
  negative := Scratch.cellRef scratch .divisionNegative
  wideNumerator := Scratch.cellRef scratch .divisionWideNumerator
  wideDenominator := Scratch.cellRef scratch .divisionWideDenominator
  division := Scratch.cellRef scratch .divisionQuotientRemainder
  magnitudeRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .divisionMagnitude
  negativeRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .divisionNegative
  wideNumeratorRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch
      .divisionWideNumerator
  wideDenominatorRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch
      .divisionWideDenominator
  divisionRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch
      .divisionQuotientRemainder
  outputWritable := Or.inl
    (LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .thirdOutput)

/-- Third-coordinate scratch view, using `g11` as denominator magnitude. -/
def thirdScratchRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) :
    LatticeNearestPlaneThree.ThirdScratchRefs ctx (Scratch.Width N) where
  cross := crossRefs scratch
  productLeft := Scratch.cellRef scratch .crossProductLeft
  productLeftRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .crossProductLeft
  productRight := Scratch.cellRef scratch .crossProductRight
  productRightRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .crossProductRight
  dotProduct := Scratch.cellRef scratch .dotProduct
  dotProductRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .dotProduct
  numerator := Scratch.cellRef scratch .numerator
  numeratorRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .numerator
  denominator := Scratch.cellRef scratch .denominator
  denominatorRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .denominator
  denominatorMagnitude := Scratch.cellRef scratch .g11
  denominatorMagnitudeRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .g11
  division := thirdDivisionRefs scratch
  reduceProduct := Scratch.cellRef scratch .reduceProduct
  reduceProductRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .reduceProduct
  divisionNumerator := rfl
  divisionDenominator := rfl

/-- Rounded-division body whose quotient persists as the second coefficient. -/
def secondDivisionRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) :
    RoundedDiv.BodyRefs ctx (Scratch.Width N) where
  numerator := SignedWord.writeInput (Scratch.cellRef scratch .numerator)
  denominator := SignedWord.writeInput (Scratch.cellRef scratch .denominator)
  output := Scratch.cellRef scratch .secondOutput
  magnitude := Scratch.cellRef scratch .divisionMagnitude
  negative := Scratch.cellRef scratch .divisionNegative
  wideNumerator := Scratch.cellRef scratch .divisionWideNumerator
  wideDenominator := Scratch.cellRef scratch .divisionWideDenominator
  division := Scratch.cellRef scratch .divisionQuotientRemainder
  magnitudeRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .divisionMagnitude
  negativeRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .divisionNegative
  wideNumeratorRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch
      .divisionWideNumerator
  wideDenominatorRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch
      .divisionWideDenominator
  divisionRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch
      .divisionQuotientRemainder
  outputWritable := Or.inl
    (LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .secondOutput)

/-- Complete second-coordinate scratch view. -/
def secondScratchRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) :
    LatticeNearestPlaneThree.SecondScratchRefs ctx (Scratch.Width N) where
  cross := crossRefs scratch
  crossProductLeft := Scratch.cellRef scratch .crossProductLeft
  crossProductLeftRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .crossProductLeft
  crossProductRight := Scratch.cellRef scratch .crossProductRight
  crossProductRightRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .crossProductRight
  dotProduct := Scratch.cellRef scratch .dotProduct
  dotProductRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .dotProduct
  g11 := Scratch.cellRef scratch .g11
  g11Role := LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .g11
  g21 := Scratch.cellRef scratch .g21
  g21Role := LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .g21
  targetDotSecond := Scratch.cellRef scratch .targetDotSecond
  targetDotSecondRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .targetDotSecond
  targetDotFirst := Scratch.cellRef scratch .targetDotFirst
  targetDotFirstRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .targetDotFirst
  numerator := Scratch.cellRef scratch .numerator
  numeratorRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .numerator
  numeratorProduct := Scratch.cellRef scratch .numeratorProduct
  numeratorProductRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .numeratorProduct
  denominator := Scratch.cellRef scratch .denominator
  denominatorRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .denominator
  division := secondDivisionRefs scratch
  reduceProduct := Scratch.cellRef scratch .reduceProduct
  reduceProductRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .reduceProduct
  divisionNumerator := rfl
  divisionDenominator := rfl

/-- Final rounded-division body, reusing `targetDotSecond` as its output. -/
def firstDivisionRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) :
    RoundedDiv.BodyRefs ctx (Scratch.Width N) where
  numerator := SignedWord.writeInput (Scratch.cellRef scratch .numerator)
  denominator := SignedWord.writeInput (Scratch.cellRef scratch .denominator)
  output := Scratch.cellRef scratch .targetDotSecond
  magnitude := Scratch.cellRef scratch .divisionMagnitude
  negative := Scratch.cellRef scratch .divisionNegative
  wideNumerator := Scratch.cellRef scratch .divisionWideNumerator
  wideDenominator := Scratch.cellRef scratch .divisionWideDenominator
  division := Scratch.cellRef scratch .divisionQuotientRemainder
  magnitudeRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .divisionMagnitude
  negativeRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .divisionNegative
  wideNumeratorRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch
      .divisionWideNumerator
  wideDenominatorRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch
      .divisionWideDenominator
  divisionRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch
      .divisionQuotientRemainder
  outputWritable := Or.inl
    (LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .targetDotSecond)

/-- Final first-coordinate scratch view. -/
def firstScratchRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) :
    LatticeNearestPlaneThree.FirstScratchRefs ctx (Scratch.Width N) where
  dotProduct := Scratch.cellRef scratch .dotProduct
  dotProductRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .dotProduct
  numerator := Scratch.cellRef scratch .numerator
  numeratorRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .numerator
  normProduct := Scratch.cellRef scratch .numeratorProduct
  normProductRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .numeratorProduct
  denominator := Scratch.cellRef scratch .denominator
  denominatorRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .denominator
  division := firstDivisionRefs scratch
  reduceProduct := Scratch.cellRef scratch .reduceProduct
  reduceProductRole :=
    LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role scratch .reduceProduct
  divisionNumerator := rfl
  divisionDenominator := rfl

/-- Full three-stage nearest-plane view over the persistent basis and target. -/
def nearestRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : State.Cells ctx N) (scratch : Scratch.Cells ctx N) :
    LatticeNearestPlaneThree.Refs ctx (Scratch.Width N) where
  basis := LatticePairStateWorkspaceViews.basisRefs state
  target := LatticePairStateWorkspaceViews.targetRefs state
  third := thirdScratchRefs scratch
  second := secondScratchRefs scratch
  first := firstScratchRefs scratch

/-- Complete wide-LLL followed by three-stage nearest-plane reference package. -/
def pairRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : State.Cells ctx N)
    (targetScratch : LatticeWideTargetWorkspaceViews.Scratch.Cells ctx N)
    (lllScratch : LatticeFixedFuelScratchWorkspaceViews.Scratch.Cells ctx N)
    (nearestScratch : Scratch.Cells ctx N) (pair : BatchMachine.PairRefs ctx N) :
    LatticePairNearestPlaneMachine.Refs ctx N where
  wide := LatticeWideLllWorkspaceViews.wideRefs
    state targetScratch lllScratch pair
  third := thirdScratchRefs nearestScratch
  second := secondScratchRefs nearestScratch
  first := firstScratchRefs nearestScratch

end

end LatticeNearestPlaneScratchWorkspaceViews
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
