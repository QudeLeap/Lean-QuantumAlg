/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Workspace.Separation.Second

/-!
# First-coordinate physical separation
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical
namespace LatticeNearestPlaneScratchWorkspaceSeparation

open Execution
open ClassicalRoutines.NumberTheory

noncomputable section

/-- The second-phase key inventory also separates the first-coordinate
numerator refresh, which reuses the same physical scratch. -/
lemma firstNumeratorDotSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeNearestPlaneThree.firstRefs
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
    LatticeDotRefresh.Separation refs.target refs.basis.first
      (LatticeNearestPlaneFirst.numeratorDotRefs refs) := by
  let allRefs := LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
    state scratch
  let phaseRefs := LatticeNearestPlaneThree.secondRefs allRefs
  let refs := LatticeNearestPlaneThree.firstRefs allRefs
  change LatticeDotRefresh.Separation refs.target refs.basis.first
    (LatticeNearestPlaneFirst.numeratorDotRefs refs)
  have phase : LatticeNearestPlaneSecond.PhaseSeparation phaseRefs :=
    secondPhaseSeparation certificates
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · exact secondDotCoordinateSeparation phaseRefs phase refs.target.first
      refs.basis.first.first refs.numerator refs.dotProduct .targetFirst
      .basisFirstFirst .numerator .dotProduct rfl rfl rfl rfl (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact secondDotCoordinateSeparation phaseRefs phase refs.target.second
      refs.basis.first.second refs.numerator refs.dotProduct .targetSecond
      .basisFirstSecond .numerator .dotProduct rfl rfl rfl rfl (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact secondDotCoordinateSeparation phaseRefs phase refs.target.third
      refs.basis.first.third refs.numerator refs.dotProduct .targetThird
      .basisFirstThird .numerator .dotProduct rfl rfl rfl rfl (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The second-phase key inventory also separates the first-row norm refresh,
which reuses the same physical scratch. -/
lemma firstDenominatorNormSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeNearestPlaneThree.firstRefs
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
    LatticeNormRefresh.Separation refs.basis.first
      (LatticeNearestPlaneFirst.denominatorNormRefs refs) := by
  let allRefs := LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
    state scratch
  let phaseRefs := LatticeNearestPlaneThree.secondRefs allRefs
  let refs := LatticeNearestPlaneThree.firstRefs allRefs
  change LatticeNormRefresh.Separation refs.basis.first
    (LatticeNearestPlaneFirst.denominatorNormRefs refs)
  have phase : LatticeNearestPlaneSecond.PhaseSeparation phaseRefs :=
    secondPhaseSeparation certificates
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · exact secondDotCoordinateSeparation phaseRefs phase refs.basis.first.first
      refs.basis.first.first refs.denominator refs.normProduct .basisFirstFirst
      .basisFirstFirst .denominator .numeratorProduct rfl rfl rfl rfl
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact secondDotCoordinateSeparation phaseRefs phase refs.basis.first.second
      refs.basis.first.second refs.denominator refs.normProduct .basisFirstSecond
      .basisFirstSecond .denominator .numeratorProduct rfl rfl rfl rfl
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact secondDotCoordinateSeparation phaseRefs phase refs.basis.first.third
      refs.basis.first.third refs.denominator refs.normProduct .basisFirstThird
      .basisFirstThird .denominator .numeratorProduct rfl rfl rfl rfl
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The shared physical key inventory separates the final rounded-division
body, whose output reuses the target-second dot cell. -/
lemma firstDivisionSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeNearestPlaneThree.firstRefs
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
    SignedWord.RoundedDiv.Separation refs.division := by
  let allRefs := LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
    state scratch
  let phaseRefs := LatticeNearestPlaneThree.secondRefs allRefs
  let refs := LatticeNearestPlaneThree.firstRefs allRefs
  change SignedWord.RoundedDiv.Separation refs.division
  have phase : LatticeNearestPlaneSecond.PhaseSeparation phaseRefs :=
    secondPhaseSeparation certificates
  have numeratorAvoids (target : LatticeNearestPlaneSecond.PhaseCell)
      (different : LatticeNearestPlaneSecond.PhaseCell.numerator ≠ target) :
      LatticeNearestPlaneSecond.phaseCellKey phaseRefs target ∉
        refs.division.numerator.storageKeys := by
    rw [refs.divisionNumerator]
    exact secondWriteInputAvoids phaseRefs phase refs.numerator .numerator target
      rfl different
  have denominatorAvoids (target : LatticeNearestPlaneSecond.PhaseCell)
      (different : LatticeNearestPlaneSecond.PhaseCell.denominator ≠ target) :
      LatticeNearestPlaneSecond.phaseCellKey phaseRefs target ∉
        refs.division.denominator.storageKeys := by
    rw [refs.divisionDenominator]
    exact secondWriteInputAvoids phaseRefs phase refs.denominator .denominator
      target rfl different
  have divisionKeyNe (left right : LatticeNearestPlaneSecond.PhaseCell)
      (different : left ≠ right) :
      LatticeNearestPlaneSecond.phaseCellKey phaseRefs left ≠
        LatticeNearestPlaneSecond.phaseCellKey phaseRefs right :=
    phase.phaseCellKey_ne left right different
  refine {
    numeratorAvoidsMagnitude := ?_
    numeratorAvoidsNegative := ?_
    numeratorAvoidsWideNumerator := ?_
    numeratorAvoidsWideDenominator := ?_
    numeratorAvoidsDivision := ?_
    numeratorAvoidsOutput := ?_
    denominatorAvoidsMagnitude := ?_
    denominatorAvoidsNegative := ?_
    denominatorAvoidsWideNumerator := ?_
    denominatorAvoidsWideDenominator := ?_
    denominatorAvoidsDivision := ?_
    denominatorAvoidsOutput := ?_
    magnitudeNeNegative := ?_
    magnitudeNeWideNumerator := ?_
    magnitudeNeWideDenominator := ?_
    magnitudeNeDivision := ?_
    magnitudeNeOutput := ?_
    negativeNeWideNumerator := ?_
    negativeNeWideDenominator := ?_
    negativeNeDivision := ?_
    negativeNeOutput := ?_
    wideNumeratorNeWideDenominator := ?_
    wideNumeratorNeDivision := ?_
    wideNumeratorNeOutput := ?_
    wideDenominatorNeDivision := ?_
    wideDenominatorNeOutput := ?_
    divisionNeOutput := ?_ }
  · exact numeratorAvoids .divisionMagnitude (by decide)
  · exact numeratorAvoids .divisionNegative (by decide)
  · exact numeratorAvoids .divisionWideNumerator (by decide)
  · exact numeratorAvoids .divisionWideDenominator (by decide)
  · exact numeratorAvoids .divisionQuotientRemainder (by decide)
  · exact numeratorAvoids .targetDotSecond (by decide)
  · exact denominatorAvoids .divisionMagnitude (by decide)
  · exact denominatorAvoids .divisionNegative (by decide)
  · exact denominatorAvoids .divisionWideNumerator (by decide)
  · exact denominatorAvoids .divisionWideDenominator (by decide)
  · exact denominatorAvoids .divisionQuotientRemainder (by decide)
  · exact denominatorAvoids .targetDotSecond (by decide)
  · exact divisionKeyNe .divisionMagnitude .divisionNegative (by decide)
  · exact divisionKeyNe .divisionMagnitude .divisionWideNumerator (by decide)
  · exact divisionKeyNe .divisionMagnitude .divisionWideDenominator (by decide)
  · exact divisionKeyNe .divisionMagnitude .divisionQuotientRemainder (by decide)
  · exact divisionKeyNe .divisionMagnitude .targetDotSecond (by decide)
  · exact divisionKeyNe .divisionNegative .divisionWideNumerator (by decide)
  · exact divisionKeyNe .divisionNegative .divisionWideDenominator (by decide)
  · exact divisionKeyNe .divisionNegative .divisionQuotientRemainder (by decide)
  · exact divisionKeyNe .divisionNegative .targetDotSecond (by decide)
  · exact divisionKeyNe .divisionWideNumerator .divisionWideDenominator (by decide)
  · exact divisionKeyNe .divisionWideNumerator .divisionQuotientRemainder (by decide)
  · exact divisionKeyNe .divisionWideNumerator .targetDotSecond (by decide)
  · exact divisionKeyNe .divisionWideDenominator .divisionQuotientRemainder (by decide)
  · exact divisionKeyNe .divisionWideDenominator .targetDotSecond (by decide)
  · exact divisionKeyNe .divisionQuotientRemainder .targetDotSecond (by decide)

private lemma firstReduceCoordinateSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (phaseRefs : LatticeNearestPlaneSecond.Refs ctx width)
    (phase : LatticeNearestPlaneSecond.PhaseSeparation phaseRefs)
    (refs : LatticeNearestPlaneFirst.Refs ctx width)
    (source target : CWriteRef ctx (LatticeState.RawSignedWordShape width))
    (sourceCell targetCell : LatticeNearestPlaneSecond.PhaseCell)
    (sourceKey : source.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey phaseRefs sourceCell)
    (targetKey : target.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey phaseRefs targetCell)
    (coefficientKey : refs.division.output.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey phaseRefs .targetDotSecond)
    (productKey : refs.reduceProduct.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey phaseRefs .reduceProduct)
    (sourceNeProduct : sourceCell ≠ .reduceProduct)
    (targetNeProduct : targetCell ≠ .reduceProduct)
    (coefficientNeTarget :
      LatticeNearestPlaneSecond.PhaseCell.targetDotSecond ≠ targetCell)
    (sourceNeTarget : sourceCell ≠ targetCell)
    (productNeTarget :
      LatticeNearestPlaneSecond.PhaseCell.reduceProduct ≠ targetCell) :
    LatticeArithmetic.CoordinateReduceSeparation
      (SignedWord.writeInput refs.division.output)
      (LatticeState.coordinateInput source) target refs.reduceProduct := by
  refine {
    coefficientAvoidsProduct := ?_
    sourceAvoidsProduct := ?_
    targetAvoidsProduct := ?_
    coefficientAvoidsTarget := ?_
    sourceAvoidsTarget := ?_
    productAvoidsTarget := ?_ }
  · exact secondWriteInputAvoidsWrite phaseRefs phase refs.division.output
      refs.reduceProduct .targetDotSecond .reduceProduct coefficientKey
        productKey (by decide)
  · exact secondCoordinateAvoidsWrite phaseRefs phase source refs.reduceProduct
      sourceCell .reduceProduct sourceKey productKey sourceNeProduct
  · exact secondWriteInputAvoidsWrite phaseRefs phase target refs.reduceProduct
      targetCell .reduceProduct targetKey productKey targetNeProduct
  · exact secondWriteInputAvoidsWrite phaseRefs phase refs.division.output target
      .targetDotSecond targetCell coefficientKey targetKey coefficientNeTarget
  · exact secondCoordinateAvoidsWrite phaseRefs phase source target sourceCell
      targetCell sourceKey targetKey sourceNeTarget
  · exact secondWriteInputAvoidsWrite phaseRefs phase refs.reduceProduct target
      .reduceProduct targetCell productKey targetKey productNeTarget

/-- The shared physical key inventory separates the final first-coordinate
point reduction. -/
lemma firstReductionSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeNearestPlaneThree.firstRefs
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
    LatticeArithmetic.PointReduceSeparation
      (SignedWord.writeInput refs.division.output) refs.basis.first refs.target
        refs.reduceProduct := by
  let allRefs := LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
    state scratch
  let phaseRefs := LatticeNearestPlaneThree.secondRefs allRefs
  let refs := LatticeNearestPlaneThree.firstRefs allRefs
  change LatticeArithmetic.PointReduceSeparation
    (SignedWord.writeInput refs.division.output) refs.basis.first refs.target
      refs.reduceProduct
  have phase : LatticeNearestPlaneSecond.PhaseSeparation phaseRefs :=
    secondPhaseSeparation certificates
  refine {
    first := ?_
    second := ?_
    third := ?_
    sourceSecondAvoidsFirstTarget := ?_
    sourceThirdAvoidsFirstTarget := ?_
    sourceThirdAvoidsSecondTarget := ?_
    targetFirstAvoidsSecond := ?_
    targetFirstAvoidsThird := ?_
    targetSecondAvoidsFirst := ?_
    targetSecondAvoidsThird := ?_
    targetThirdAvoidsFirst := ?_
    targetThirdAvoidsSecond := ?_ }
  · exact firstReduceCoordinateSeparation phaseRefs phase refs
      refs.basis.first.first refs.target.first .basisFirstFirst .targetFirst
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
          (by decide)
  · exact firstReduceCoordinateSeparation phaseRefs phase refs
      refs.basis.first.second refs.target.second .basisFirstSecond .targetSecond
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
          (by decide)
  · exact firstReduceCoordinateSeparation phaseRefs phase refs
      refs.basis.first.third refs.target.third .basisFirstThird .targetThird
        rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
          (by decide)
  · exact secondCoordinateAvoidsWrite phaseRefs phase refs.basis.first.second
      refs.target.first .basisFirstSecond .targetFirst rfl rfl (by decide)
  · exact secondCoordinateAvoidsWrite phaseRefs phase refs.basis.first.third
      refs.target.first .basisFirstThird .targetFirst rfl rfl (by decide)
  · exact secondCoordinateAvoidsWrite phaseRefs phase refs.basis.first.third
      refs.target.second .basisFirstThird .targetSecond rfl rfl (by decide)
  · exact secondWriteInputAvoidsWrite phaseRefs phase refs.target.first
      refs.target.second .targetFirst .targetSecond rfl rfl (by decide)
  · exact secondWriteInputAvoidsWrite phaseRefs phase refs.target.first
      refs.target.third .targetFirst .targetThird rfl rfl (by decide)
  · exact secondWriteInputAvoidsWrite phaseRefs phase refs.target.second
      refs.target.first .targetSecond .targetFirst rfl rfl (by decide)
  · exact secondWriteInputAvoidsWrite phaseRefs phase refs.target.second
      refs.target.third .targetSecond .targetThird rfl rfl (by decide)
  · exact secondWriteInputAvoidsWrite phaseRefs phase refs.target.third
      refs.target.first .targetThird .targetFirst rfl rfl (by decide)
  · exact secondWriteInputAvoidsWrite phaseRefs phase refs.target.third
      refs.target.second .targetThird .targetSecond rfl rfl (by decide)

private lemma secondPointInputAvoidsPhaseCell {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (phaseRefs : LatticeNearestPlaneSecond.Refs ctx width)
    (phase : LatticeNearestPlaneSecond.PhaseSeparation phaseRefs)
    (point : LatticeState.PointRefs ctx width)
    (firstCell secondCell thirdCell target :
      LatticeNearestPlaneSecond.PhaseCell)
    (firstKey : point.first.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey phaseRefs firstCell)
    (secondKey : point.second.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey phaseRefs secondCell)
    (thirdKey : point.third.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey phaseRefs thirdCell)
    (firstDifferent : firstCell ≠ target)
    (secondDifferent : secondCell ≠ target)
    (thirdDifferent : thirdCell ≠ target) :
    LatticeNearestPlaneFirst.PointInputAvoidsKey point
      (LatticeNearestPlaneSecond.phaseCellKey phaseRefs target) := by
  refine ⟨?_, ?_, ?_⟩
  · exact secondCoordinateInputAvoids phaseRefs phase point.first firstCell
      target firstKey firstDifferent
  · exact secondCoordinateInputAvoids phaseRefs phase point.second secondCell
      target secondKey secondDifferent
  · exact secondCoordinateInputAvoids phaseRefs phase point.third thirdCell
      target thirdKey thirdDifferent

/-- The persistent state and reusable scratch package satisfy the complete
first-coordinate separation contract. -/
lemma firstSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    LatticeNearestPlaneFirst.Separation
      (LatticeNearestPlaneThree.firstRefs
        (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
          state scratch)) := by
  let allRefs := LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
    state scratch
  let phaseRefs := LatticeNearestPlaneThree.secondRefs allRefs
  let refs := LatticeNearestPlaneThree.firstRefs allRefs
  change LatticeNearestPlaneFirst.Separation refs
  have phase : LatticeNearestPlaneSecond.PhaseSeparation phaseRefs :=
    secondPhaseSeparation certificates
  have targetAvoids (target : LatticeNearestPlaneSecond.PhaseCell)
      (firstDifferent :
        LatticeNearestPlaneSecond.PhaseCell.targetFirst ≠ target)
      (secondDifferent :
        LatticeNearestPlaneSecond.PhaseCell.targetSecond ≠ target)
      (thirdDifferent :
        LatticeNearestPlaneSecond.PhaseCell.targetThird ≠ target) :
      LatticeNearestPlaneFirst.PointInputAvoidsKey refs.target
        (LatticeNearestPlaneSecond.phaseCellKey phaseRefs target) :=
    secondPointInputAvoidsPhaseCell phaseRefs phase refs.target .targetFirst
      .targetSecond .targetThird target rfl rfl rfl firstDifferent
        secondDifferent thirdDifferent
  have basisFirstAvoids (target : LatticeNearestPlaneSecond.PhaseCell)
      (firstDifferent :
        LatticeNearestPlaneSecond.PhaseCell.basisFirstFirst ≠ target)
      (secondDifferent :
        LatticeNearestPlaneSecond.PhaseCell.basisFirstSecond ≠ target)
      (thirdDifferent :
        LatticeNearestPlaneSecond.PhaseCell.basisFirstThird ≠ target) :
      LatticeNearestPlaneFirst.PointInputAvoidsKey refs.basis.first
        (LatticeNearestPlaneSecond.phaseCellKey phaseRefs target) :=
    secondPointInputAvoidsPhaseCell phaseRefs phase refs.basis.first
      .basisFirstFirst .basisFirstSecond .basisFirstThird target rfl rfl rfl
        firstDifferent secondDifferent thirdDifferent
  have magnitudeKey : refs.division.magnitude.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey phaseRefs .divisionMagnitude := rfl
  have negativeKey : refs.division.negative.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey phaseRefs .divisionNegative := rfl
  have wideNumeratorKey : refs.division.wideNumerator.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey phaseRefs
        .divisionWideNumerator := rfl
  have wideDenominatorKey : refs.division.wideDenominator.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey phaseRefs
        .divisionWideDenominator := rfl
  have divisionKey : refs.division.division.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey phaseRefs
        .divisionQuotientRemainder := rfl
  have outputKey : refs.division.output.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey phaseRefs .targetDotSecond := rfl
  have basisFirstAvoidsDivision :
      ∀ key ∈ SignedWord.RoundedDiv.mutableKeys refs.division,
        LatticeNearestPlaneFirst.PointInputAvoidsKey refs.basis.first key := by
    intro key member
    simp only [SignedWord.RoundedDiv.mutableKeys, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [magnitudeKey]
      exact basisFirstAvoids .divisionMagnitude (by decide) (by decide)
        (by decide)
    · rw [negativeKey]
      exact basisFirstAvoids .divisionNegative (by decide) (by decide)
        (by decide)
    · rw [wideNumeratorKey]
      exact basisFirstAvoids .divisionWideNumerator (by decide) (by decide)
        (by decide)
    · rw [wideDenominatorKey]
      exact basisFirstAvoids .divisionWideDenominator (by decide) (by decide)
        (by decide)
    · rw [divisionKey]
      exact basisFirstAvoids .divisionQuotientRemainder (by decide) (by decide)
        (by decide)
    · rw [outputKey]
      exact basisFirstAvoids .targetDotSecond (by decide) (by decide)
        (by decide)
  have targetAvoidsDivision :
      ∀ key ∈ SignedWord.RoundedDiv.mutableKeys refs.division,
        LatticeNearestPlaneFirst.PointInputAvoidsKey refs.target key := by
    intro key member
    simp only [SignedWord.RoundedDiv.mutableKeys, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [magnitudeKey]
      exact targetAvoids .divisionMagnitude (by decide) (by decide) (by decide)
    · rw [negativeKey]
      exact targetAvoids .divisionNegative (by decide) (by decide) (by decide)
    · rw [wideNumeratorKey]
      exact targetAvoids .divisionWideNumerator (by decide) (by decide)
        (by decide)
    · rw [wideDenominatorKey]
      exact targetAvoids .divisionWideDenominator (by decide) (by decide)
        (by decide)
    · rw [divisionKey]
      exact targetAvoids .divisionQuotientRemainder (by decide) (by decide)
        (by decide)
    · rw [outputKey]
      exact targetAvoids .targetDotSecond (by decide) (by decide) (by decide)
  refine {
    numeratorDot := firstNumeratorDotSeparation certificates
    denominatorNorm := firstDenominatorNormSeparation certificates
    numeratorAvoidsDenominator := ?_
    numeratorAvoidsNormProduct := ?_
    targetAvoidsDenominator := ?_
    targetAvoidsNormProduct := ?_
    basisFirstAvoidsDivision := basisFirstAvoidsDivision
    targetAvoidsDivision := targetAvoidsDivision
    division := firstDivisionSeparation certificates
    reduction := firstReductionSeparation certificates }
  · exact secondWriteInputAvoidsWrite phaseRefs phase refs.numerator
      refs.denominator .numerator .denominator rfl rfl (by decide)
  · exact secondWriteInputAvoidsWrite phaseRefs phase refs.numerator
      refs.normProduct .numerator .numeratorProduct rfl rfl (by decide)
  · exact targetAvoids .denominator (by decide) (by decide) (by decide)
  · exact targetAvoids .numeratorProduct (by decide) (by decide) (by decide)

end

end LatticeNearestPlaneScratchWorkspaceSeparation
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical
