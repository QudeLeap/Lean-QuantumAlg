/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Workspace.Separation.Keys

/-!
# Second-coordinate physical separation
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical
namespace LatticeNearestPlaneScratchWorkspaceSeparation

open Execution
open ClassicalRoutines.NumberTheory

noncomputable section

/-- Unified physical cell underlying one second-phase semantic cell. -/
def secondCell : LatticeNearestPlaneSecond.PhaseCell → PhysicalCell
  | .basisFirstFirst => .inl .basis11
  | .basisFirstSecond => .inl .basis12
  | .basisFirstThird => .inl .basis13
  | .basisSecondFirst => .inl .basis21
  | .basisSecondSecond => .inl .basis22
  | .basisSecondThird => .inl .basis23
  | .targetFirst => .inl .targetFirst
  | .targetSecond => .inl .targetSecond
  | .targetThird => .inl .targetThird
  | .crossFirst => .inr .crossFirst
  | .crossSecond => .inr .crossSecond
  | .crossThird => .inr .crossThird
  | .crossProductLeft => .inr .crossProductLeft
  | .crossProductRight => .inr .crossProductRight
  | .dotProduct => .inr .dotProduct
  | .g11 => .inr .g11
  | .g21 => .inr .g21
  | .targetDotSecond => .inr .targetDotSecond
  | .targetDotFirst => .inr .targetDotFirst
  | .numerator => .inr .numerator
  | .numeratorProduct => .inr .numeratorProduct
  | .denominator => .inr .denominator
  | .divisionMagnitude => .inr .divisionMagnitude
  | .divisionNegative => .inr .divisionNegative
  | .divisionWideNumerator => .inr .divisionWideNumerator
  | .divisionWideDenominator => .inr .divisionWideDenominator
  | .divisionQuotientRemainder => .inr .divisionQuotientRemainder
  | .divisionOutput => .inr .secondOutput
  | .reduceProduct => .inr .reduceProduct

private def secondCellInverse : PhysicalCell →
    Option LatticeNearestPlaneSecond.PhaseCell
  | .inl .basis11 => some .basisFirstFirst
  | .inl .basis12 => some .basisFirstSecond
  | .inl .basis13 => some .basisFirstThird
  | .inl .basis21 => some .basisSecondFirst
  | .inl .basis22 => some .basisSecondSecond
  | .inl .basis23 => some .basisSecondThird
  | .inl .targetFirst => some .targetFirst
  | .inl .targetSecond => some .targetSecond
  | .inl .targetThird => some .targetThird
  | .inr .crossFirst => some .crossFirst
  | .inr .crossSecond => some .crossSecond
  | .inr .crossThird => some .crossThird
  | .inr .crossProductLeft => some .crossProductLeft
  | .inr .crossProductRight => some .crossProductRight
  | .inr .dotProduct => some .dotProduct
  | .inr .g11 => some .g11
  | .inr .g21 => some .g21
  | .inr .targetDotSecond => some .targetDotSecond
  | .inr .targetDotFirst => some .targetDotFirst
  | .inr .numerator => some .numerator
  | .inr .numeratorProduct => some .numeratorProduct
  | .inr .denominator => some .denominator
  | .inr .divisionMagnitude => some .divisionMagnitude
  | .inr .divisionNegative => some .divisionNegative
  | .inr .divisionWideNumerator => some .divisionWideNumerator
  | .inr .divisionWideDenominator => some .divisionWideDenominator
  | .inr .divisionQuotientRemainder => some .divisionQuotientRemainder
  | .inr .secondOutput => some .divisionOutput
  | .inr .reduceProduct => some .reduceProduct
  | _ => none

private lemma secondCellInverse_apply
    (cell : LatticeNearestPlaneSecond.PhaseCell) :
    secondCellInverse (secondCell cell) = some cell := by
  cases cell <;> rfl

/-- The second-phase semantic projection is injective. -/
lemma secondCell_injective : Function.Injective secondCell := by
  intro left right equal
  have mapped := congrArg secondCellInverse equal
  rw [secondCellInverse_apply, secondCellInverse_apply] at mapped
  exact Option.some.inj mapped

/-- Second-phase semantic keys are their unified physical keys. -/
lemma secondCellKey_eq_physicalKey {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N)
    (cell : LatticeNearestPlaneSecond.PhaseCell) :
    LatticeNearestPlaneSecond.phaseCellKey
        (LatticeNearestPlaneThree.secondRefs
          (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs state scratch)) cell =
      physicalKey state scratch (secondCell cell) := by
  cases cell <;> rfl

/-- Physical packages supply the second-phase global key separation. -/
lemma secondPhaseSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    LatticeNearestPlaneSecond.PhaseSeparation
      (LatticeNearestPlaneThree.secondRefs
        (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
          state scratch)) := by
  refine ⟨?_⟩
  intro left right equal
  apply secondCell_injective
  apply physicalKey_injective certificates
  simpa only [secondCellKey_eq_physicalKey] using equal

private def secondCrossMutableCell : LatticeCross.MutableCell →
    LatticeNearestPlaneSecond.PhaseCell
  | .outputFirst => .crossFirst
  | .outputSecond => .crossSecond
  | .outputThird => .crossThird
  | .productLeft => .crossProductLeft
  | .productRight => .crossProductRight

private lemma secondCrossMutableCell_injective :
    Function.Injective secondCrossMutableCell := by
  intro left right equal
  cases left <;> cases right <;> cases equal <;> rfl

private lemma secondCrossMutableKey {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeNearestPlaneSecond.Refs ctx width)
    (cell : LatticeCross.MutableCell) :
    LatticeCross.mutableKey refs.cross refs.crossProductLeft
        refs.crossProductRight cell =
      LatticeNearestPlaneSecond.phaseCellKey refs
        (secondCrossMutableCell cell) := by
  cases cell <;> rfl

private def secondCrossSourceCell : LatticeCross.SourceCell →
    LatticeNearestPlaneSecond.PhaseCell
  | .leftFirst => .basisFirstFirst
  | .leftSecond => .basisFirstSecond
  | .leftThird => .basisFirstThird
  | .rightFirst => .basisSecondFirst
  | .rightSecond => .basisSecondSecond
  | .rightThird => .basisSecondThird

/-- Physical phase separation supplies the complete second-coordinate cross
product subcontract. -/
lemma secondCrossSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeNearestPlaneThree.secondRefs
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
    LatticeCross.PointCrossSeparation refs.basis.first refs.basis.second
      refs.cross refs.crossProductLeft refs.crossProductRight := by
  let refs := LatticeNearestPlaneThree.secondRefs
    (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
      state scratch)
  change LatticeCross.PointCrossSeparation refs.basis.first refs.basis.second
    refs.cross refs.crossProductLeft refs.crossProductRight
  have phase : LatticeNearestPlaneSecond.PhaseSeparation refs :=
    secondPhaseSeparation certificates
  refine {
    sourceAvoidsMutable := ?_
    mutableInjective := ?_ }
  · intro source target
    have keyNe := phase.phaseCellKey_ne (secondCrossSourceCell source)
      (secondCrossMutableCell target) (by
        cases source <;> cases target <;> decide)
    cases source <;> cases target <;>
      apply storageRead_not_mem <;> exact keyNe
  · intro left right equal
    apply secondCrossMutableCell_injective
    apply phase.keyInjective
    simpa only [secondCrossMutableKey] using equal

private lemma secondWriteInputAvoids {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} {shape : CShape}
    (refs : LatticeNearestPlaneSecond.Refs ctx width)
    (phase : LatticeNearestPlaneSecond.PhaseSeparation refs)
    (source : CWriteRef ctx shape)
    (sourceCell target : LatticeNearestPlaneSecond.PhaseCell)
    (sourceKey : source.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey refs sourceCell)
    (different : sourceCell ≠ target) :
    LatticeNearestPlaneSecond.phaseCellKey refs target ∉
      (SignedWord.writeInput source).storageKeys := by
  apply storageRead_not_mem
  rw [sourceKey]
  exact phase.phaseCellKey_ne sourceCell target different

private lemma secondCoordinateInputAvoids {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeNearestPlaneSecond.Refs ctx width)
    (phase : LatticeNearestPlaneSecond.PhaseSeparation refs)
    (source : CWriteRef ctx (LatticeState.RawSignedWordShape width))
    (sourceCell target : LatticeNearestPlaneSecond.PhaseCell)
    (sourceKey : source.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey refs sourceCell)
    (different : sourceCell ≠ target) :
    LatticeNearestPlaneSecond.phaseCellKey refs target ∉
      (LatticeState.coordinateInput source).storageKeys := by
  apply storageRead_not_mem
  rw [sourceKey]
  exact phase.phaseCellKey_ne sourceCell target different

private lemma secondDotCoordinateSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeNearestPlaneSecond.Refs ctx width)
    (phase : LatticeNearestPlaneSecond.PhaseSeparation refs)
    (left right accumulator product :
      CWriteRef ctx (LatticeState.RawSignedWordShape width))
    (leftCell rightCell accumulatorCell productCell :
      LatticeNearestPlaneSecond.PhaseCell)
    (leftKey : left.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey refs leftCell)
    (rightKey : right.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey refs rightCell)
    (accumulatorKey : accumulator.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey refs accumulatorCell)
    (productKey : product.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey refs productCell)
    (leftNeProduct : leftCell ≠ productCell)
    (rightNeProduct : rightCell ≠ productCell)
    (accumulatorNeProduct : accumulatorCell ≠ productCell)
    (leftNeAccumulator : leftCell ≠ accumulatorCell)
    (rightNeAccumulator : rightCell ≠ accumulatorCell)
    (productNeAccumulator : productCell ≠ accumulatorCell) :
    LatticeDot.CoordinateAccumulateSeparation
      (LatticeState.coordinateInput left)
      (LatticeState.coordinateInput right) accumulator product := by
  refine {
    leftAvoidsProduct := ?_
    rightAvoidsProduct := ?_
    accumulatorAvoidsProduct := ?_
    leftAvoidsAccumulator := ?_
    rightAvoidsAccumulator := ?_
    productAvoidsAccumulator := ?_ }
  · rw [productKey]
    exact secondCoordinateInputAvoids refs phase left leftCell productCell
      leftKey leftNeProduct
  · rw [productKey]
    exact secondCoordinateInputAvoids refs phase right rightCell productCell
      rightKey rightNeProduct
  · rw [productKey]
    exact secondWriteInputAvoids refs phase accumulator accumulatorCell
      productCell accumulatorKey accumulatorNeProduct
  · rw [accumulatorKey]
    exact secondCoordinateInputAvoids refs phase left leftCell accumulatorCell
      leftKey leftNeAccumulator
  · rw [accumulatorKey]
    exact secondCoordinateInputAvoids refs phase right rightCell accumulatorCell
      rightKey rightNeAccumulator
  · rw [accumulatorKey]
    exact secondWriteInputAvoids refs phase product productCell accumulatorCell
      productKey productNeAccumulator

/-- Physical phase separation supplies the refreshed `g11` dot product. -/
lemma secondG11DotSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeNearestPlaneThree.secondRefs
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
    LatticeDotRefresh.Separation refs.basis.first refs.basis.first
      (LatticeNearestPlaneSecond.g11DotRefs refs) := by
  let refs := LatticeNearestPlaneThree.secondRefs
    (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
      state scratch)
  change LatticeDotRefresh.Separation refs.basis.first refs.basis.first
    (LatticeNearestPlaneSecond.g11DotRefs refs)
  have phase : LatticeNearestPlaneSecond.PhaseSeparation refs :=
    secondPhaseSeparation certificates
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · exact secondDotCoordinateSeparation refs phase refs.basis.first.first
      refs.basis.first.first refs.g11 refs.dotProduct .basisFirstFirst
      .basisFirstFirst .g11 .dotProduct rfl rfl rfl rfl (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact secondDotCoordinateSeparation refs phase refs.basis.first.second
      refs.basis.first.second refs.g11 refs.dotProduct .basisFirstSecond
      .basisFirstSecond .g11 .dotProduct rfl rfl rfl rfl (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact secondDotCoordinateSeparation refs phase refs.basis.first.third
      refs.basis.first.third refs.g11 refs.dotProduct .basisFirstThird
      .basisFirstThird .g11 .dotProduct rfl rfl rfl rfl (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Physical phase separation supplies the refreshed `g21` dot product. -/
lemma secondG21DotSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeNearestPlaneThree.secondRefs
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
    LatticeDotRefresh.Separation refs.basis.second refs.basis.first
      (LatticeNearestPlaneSecond.g21DotRefs refs) := by
  let refs := LatticeNearestPlaneThree.secondRefs
    (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
      state scratch)
  change LatticeDotRefresh.Separation refs.basis.second refs.basis.first
    (LatticeNearestPlaneSecond.g21DotRefs refs)
  have phase : LatticeNearestPlaneSecond.PhaseSeparation refs :=
    secondPhaseSeparation certificates
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · exact secondDotCoordinateSeparation refs phase refs.basis.second.first
      refs.basis.first.first refs.g21 refs.dotProduct .basisSecondFirst
      .basisFirstFirst .g21 .dotProduct rfl rfl rfl rfl (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact secondDotCoordinateSeparation refs phase refs.basis.second.second
      refs.basis.first.second refs.g21 refs.dotProduct .basisSecondSecond
      .basisFirstSecond .g21 .dotProduct rfl rfl rfl rfl (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact secondDotCoordinateSeparation refs phase refs.basis.second.third
      refs.basis.first.third refs.g21 refs.dotProduct .basisSecondThird
      .basisFirstThird .g21 .dotProduct rfl rfl rfl rfl (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Physical phase separation supplies the refreshed target-second dot
product. -/
lemma secondTargetSecondDotSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeNearestPlaneThree.secondRefs
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
    LatticeDotRefresh.Separation refs.target refs.basis.second
      (LatticeNearestPlaneSecond.targetSecondDotRefs refs) := by
  let refs := LatticeNearestPlaneThree.secondRefs
    (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
      state scratch)
  change LatticeDotRefresh.Separation refs.target refs.basis.second
    (LatticeNearestPlaneSecond.targetSecondDotRefs refs)
  have phase : LatticeNearestPlaneSecond.PhaseSeparation refs :=
    secondPhaseSeparation certificates
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · exact secondDotCoordinateSeparation refs phase refs.target.first
      refs.basis.second.first refs.targetDotSecond refs.dotProduct .targetFirst
      .basisSecondFirst .targetDotSecond .dotProduct rfl rfl rfl rfl
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact secondDotCoordinateSeparation refs phase refs.target.second
      refs.basis.second.second refs.targetDotSecond refs.dotProduct .targetSecond
      .basisSecondSecond .targetDotSecond .dotProduct rfl rfl rfl rfl
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact secondDotCoordinateSeparation refs phase refs.target.third
      refs.basis.second.third refs.targetDotSecond refs.dotProduct .targetThird
      .basisSecondThird .targetDotSecond .dotProduct rfl rfl rfl rfl
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Physical phase separation supplies the refreshed target-first dot
product. -/
lemma secondTargetFirstDotSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeNearestPlaneThree.secondRefs
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
    LatticeDotRefresh.Separation refs.target refs.basis.first
      (LatticeNearestPlaneSecond.targetFirstDotRefs refs) := by
  let refs := LatticeNearestPlaneThree.secondRefs
    (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
      state scratch)
  change LatticeDotRefresh.Separation refs.target refs.basis.first
    (LatticeNearestPlaneSecond.targetFirstDotRefs refs)
  have phase : LatticeNearestPlaneSecond.PhaseSeparation refs :=
    secondPhaseSeparation certificates
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · exact secondDotCoordinateSeparation refs phase refs.target.first
      refs.basis.first.first refs.targetDotFirst refs.dotProduct .targetFirst
      .basisFirstFirst .targetDotFirst .dotProduct rfl rfl rfl rfl
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact secondDotCoordinateSeparation refs phase refs.target.second
      refs.basis.first.second refs.targetDotFirst refs.dotProduct .targetSecond
      .basisFirstSecond .targetDotFirst .dotProduct rfl rfl rfl rfl
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact secondDotCoordinateSeparation refs phase refs.target.third
      refs.basis.first.third refs.targetDotFirst refs.dotProduct .targetThird
      .basisFirstThird .targetDotFirst .dotProduct rfl rfl rfl rfl
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Physical phase separation supplies the refreshed second-coordinate
denominator dot product. -/
lemma secondDenominatorDotSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeNearestPlaneThree.secondRefs
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
    LatticeDotRefresh.Separation refs.cross refs.cross
      (LatticeNearestPlaneSecond.denominatorDotRefs refs) := by
  let refs := LatticeNearestPlaneThree.secondRefs
    (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
      state scratch)
  change LatticeDotRefresh.Separation refs.cross refs.cross
    (LatticeNearestPlaneSecond.denominatorDotRefs refs)
  have phase : LatticeNearestPlaneSecond.PhaseSeparation refs :=
    secondPhaseSeparation certificates
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · exact secondDotCoordinateSeparation refs phase refs.cross.first
      refs.cross.first refs.denominator refs.dotProduct .crossFirst .crossFirst
      .denominator .dotProduct rfl rfl rfl rfl (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
  · exact secondDotCoordinateSeparation refs phase refs.cross.second
      refs.cross.second refs.denominator refs.dotProduct .crossSecond .crossSecond
      .denominator .dotProduct rfl rfl rfl rfl (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
  · exact secondDotCoordinateSeparation refs phase refs.cross.third
      refs.cross.third refs.denominator refs.dotProduct .crossThird .crossThird
      .denominator .dotProduct rfl rfl rfl rfl (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)

/-- Physical phase separation supplies the second-coordinate rounded-division
subcontract. -/
lemma secondDivisionSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeNearestPlaneThree.secondRefs
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
    SignedWord.RoundedDiv.Separation refs.division := by
  let refs := LatticeNearestPlaneThree.secondRefs
    (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
      state scratch)
  change SignedWord.RoundedDiv.Separation refs.division
  have phase : LatticeNearestPlaneSecond.PhaseSeparation refs :=
    secondPhaseSeparation certificates
  have numeratorAvoids (target : LatticeNearestPlaneSecond.PhaseCell)
      (different : LatticeNearestPlaneSecond.PhaseCell.numerator ≠ target) :
      LatticeNearestPlaneSecond.phaseCellKey refs target ∉
        refs.division.numerator.storageKeys := by
    rw [refs.divisionNumerator]
    exact secondWriteInputAvoids refs phase refs.numerator .numerator target rfl
      different
  have denominatorAvoids (target : LatticeNearestPlaneSecond.PhaseCell)
      (different : LatticeNearestPlaneSecond.PhaseCell.denominator ≠ target) :
      LatticeNearestPlaneSecond.phaseCellKey refs target ∉
        refs.division.denominator.storageKeys := by
    rw [refs.divisionDenominator]
    exact secondWriteInputAvoids refs phase refs.denominator .denominator target
      rfl different
  have divisionKeyNe (left right : LatticeNearestPlaneSecond.PhaseCell)
      (different : left ≠ right) :
      LatticeNearestPlaneSecond.phaseCellKey refs left ≠
        LatticeNearestPlaneSecond.phaseCellKey refs right :=
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
  · exact numeratorAvoids .divisionOutput (by decide)
  · exact denominatorAvoids .divisionMagnitude (by decide)
  · exact denominatorAvoids .divisionNegative (by decide)
  · exact denominatorAvoids .divisionWideNumerator (by decide)
  · exact denominatorAvoids .divisionWideDenominator (by decide)
  · exact denominatorAvoids .divisionQuotientRemainder (by decide)
  · exact denominatorAvoids .divisionOutput (by decide)
  · exact divisionKeyNe .divisionMagnitude .divisionNegative (by decide)
  · exact divisionKeyNe .divisionMagnitude .divisionWideNumerator (by decide)
  · exact divisionKeyNe .divisionMagnitude .divisionWideDenominator (by decide)
  · exact divisionKeyNe .divisionMagnitude .divisionQuotientRemainder (by decide)
  · exact divisionKeyNe .divisionMagnitude .divisionOutput (by decide)
  · exact divisionKeyNe .divisionNegative .divisionWideNumerator (by decide)
  · exact divisionKeyNe .divisionNegative .divisionWideDenominator (by decide)
  · exact divisionKeyNe .divisionNegative .divisionQuotientRemainder (by decide)
  · exact divisionKeyNe .divisionNegative .divisionOutput (by decide)
  · exact divisionKeyNe .divisionWideNumerator .divisionWideDenominator (by decide)
  · exact divisionKeyNe .divisionWideNumerator .divisionQuotientRemainder (by decide)
  · exact divisionKeyNe .divisionWideNumerator .divisionOutput (by decide)
  · exact divisionKeyNe .divisionWideDenominator .divisionQuotientRemainder (by decide)
  · exact divisionKeyNe .divisionWideDenominator .divisionOutput (by decide)
  · exact divisionKeyNe .divisionQuotientRemainder .divisionOutput (by decide)

private lemma secondCoordinateAvoidsWrite {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeNearestPlaneSecond.Refs ctx width)
    (phase : LatticeNearestPlaneSecond.PhaseSeparation refs)
    (source target : CWriteRef ctx (LatticeState.RawSignedWordShape width))
    (sourceCell targetCell : LatticeNearestPlaneSecond.PhaseCell)
    (sourceKey : source.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey refs sourceCell)
    (targetKey : target.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey refs targetCell)
    (different : sourceCell ≠ targetCell) :
    target.toCStorageRef.key ∉ (LatticeState.coordinateInput source).storageKeys := by
  rw [targetKey]
  exact secondCoordinateInputAvoids refs phase source sourceCell targetCell
    sourceKey different

private lemma secondWriteInputAvoidsWrite {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeNearestPlaneSecond.Refs ctx width)
    (phase : LatticeNearestPlaneSecond.PhaseSeparation refs)
    (source target : CWriteRef ctx (LatticeState.RawSignedWordShape width))
    (sourceCell targetCell : LatticeNearestPlaneSecond.PhaseCell)
    (sourceKey : source.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey refs sourceCell)
    (targetKey : target.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey refs targetCell)
    (different : sourceCell ≠ targetCell) :
    target.toCStorageRef.key ∉ (SignedWord.writeInput source).storageKeys := by
  rw [targetKey]
  exact secondWriteInputAvoids refs phase source sourceCell targetCell sourceKey
    different

private lemma secondReduceCoordinateSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeNearestPlaneSecond.Refs ctx width)
    (phase : LatticeNearestPlaneSecond.PhaseSeparation refs)
    (source target : CWriteRef ctx (LatticeState.RawSignedWordShape width))
    (sourceCell targetCell : LatticeNearestPlaneSecond.PhaseCell)
    (sourceKey : source.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey refs sourceCell)
    (targetKey : target.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey refs targetCell)
    (sourceNeProduct : sourceCell ≠ .reduceProduct)
    (targetNeProduct : targetCell ≠ .reduceProduct)
    (coefficientNeTarget :
      LatticeNearestPlaneSecond.PhaseCell.divisionOutput ≠ targetCell)
    (sourceNeTarget : sourceCell ≠ targetCell)
    (productNeTarget :
      LatticeNearestPlaneSecond.PhaseCell.reduceProduct ≠ targetCell) :
    LatticeArithmetic.CoordinateReduceSeparation
      (SignedWord.writeInput refs.division.output)
      (LatticeState.coordinateInput source) target refs.reduceProduct := by
  have coefficientKey : refs.division.output.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey refs .divisionOutput := rfl
  have productKey : refs.reduceProduct.toCStorageRef.key =
      LatticeNearestPlaneSecond.phaseCellKey refs .reduceProduct := rfl
  refine {
    coefficientAvoidsProduct := ?_
    sourceAvoidsProduct := ?_
    targetAvoidsProduct := ?_
    coefficientAvoidsTarget := ?_
    sourceAvoidsTarget := ?_
    productAvoidsTarget := ?_ }
  · exact secondWriteInputAvoidsWrite refs phase refs.division.output
      refs.reduceProduct .divisionOutput .reduceProduct coefficientKey
        productKey (by decide)
  · exact secondCoordinateAvoidsWrite refs phase source refs.reduceProduct
      sourceCell .reduceProduct sourceKey productKey sourceNeProduct
  · exact secondWriteInputAvoidsWrite refs phase target refs.reduceProduct
      targetCell .reduceProduct targetKey productKey targetNeProduct
  · exact secondWriteInputAvoidsWrite refs phase refs.division.output target
      .divisionOutput targetCell coefficientKey targetKey coefficientNeTarget
  · exact secondCoordinateAvoidsWrite refs phase source target sourceCell
      targetCell sourceKey targetKey sourceNeTarget
  · exact secondWriteInputAvoidsWrite refs phase refs.reduceProduct target
      .reduceProduct targetCell productKey targetKey productNeTarget

/-- Physical phase separation supplies the second-coordinate point reduction
subcontract. -/
lemma secondReductionSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeNearestPlaneThree.secondRefs
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
    LatticeArithmetic.PointReduceSeparation
      (SignedWord.writeInput refs.division.output) refs.basis.second refs.target
        refs.reduceProduct := by
  let refs := LatticeNearestPlaneThree.secondRefs
    (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
      state scratch)
  change LatticeArithmetic.PointReduceSeparation
    (SignedWord.writeInput refs.division.output) refs.basis.second refs.target
      refs.reduceProduct
  have phase : LatticeNearestPlaneSecond.PhaseSeparation refs :=
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
  · exact secondReduceCoordinateSeparation refs phase refs.basis.second.first
      refs.target.first .basisSecondFirst .targetFirst rfl rfl (by decide)
        (by decide) (by decide) (by decide) (by decide)
  · exact secondReduceCoordinateSeparation refs phase refs.basis.second.second
      refs.target.second .basisSecondSecond .targetSecond rfl rfl (by decide)
        (by decide) (by decide) (by decide) (by decide)
  · exact secondReduceCoordinateSeparation refs phase refs.basis.second.third
      refs.target.third .basisSecondThird .targetThird rfl rfl (by decide)
        (by decide) (by decide) (by decide) (by decide)
  · exact secondCoordinateAvoidsWrite refs phase refs.basis.second.second
      refs.target.first .basisSecondSecond .targetFirst rfl rfl (by decide)
  · exact secondCoordinateAvoidsWrite refs phase refs.basis.second.third
      refs.target.first .basisSecondThird .targetFirst rfl rfl (by decide)
  · exact secondCoordinateAvoidsWrite refs phase refs.basis.second.third
      refs.target.second .basisSecondThird .targetSecond rfl rfl (by decide)
  · exact secondWriteInputAvoidsWrite refs phase refs.target.first
      refs.target.second .targetFirst .targetSecond rfl rfl (by decide)
  · exact secondWriteInputAvoidsWrite refs phase refs.target.first
      refs.target.third .targetFirst .targetThird rfl rfl (by decide)
  · exact secondWriteInputAvoidsWrite refs phase refs.target.second
      refs.target.first .targetSecond .targetFirst rfl rfl (by decide)
  · exact secondWriteInputAvoidsWrite refs phase refs.target.second
      refs.target.third .targetSecond .targetThird rfl rfl (by decide)
  · exact secondWriteInputAvoidsWrite refs phase refs.target.third
      refs.target.first .targetThird .targetFirst rfl rfl (by decide)
  · exact secondWriteInputAvoidsWrite refs phase refs.target.third
      refs.target.second .targetThird .targetSecond rfl rfl (by decide)

/-- The persistent state and reusable scratch package satisfy the complete
second-coordinate separation contract. -/
lemma secondSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    LatticeNearestPlaneSecond.Separation
      (LatticeNearestPlaneThree.secondRefs
        (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
          state scratch)) := by
  refine {
    phase := secondPhaseSeparation certificates
    cross := secondCrossSeparation certificates
    g11Dot := secondG11DotSeparation certificates
    g21Dot := secondG21DotSeparation certificates
    targetSecondDot := secondTargetSecondDotSeparation certificates
    targetFirstDot := secondTargetFirstDotSeparation certificates
    denominatorDot := secondDenominatorDotSeparation certificates
    division := secondDivisionSeparation certificates
    reduction := secondReductionSeparation certificates }

end

end LatticeNearestPlaneScratchWorkspaceSeparation
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical
