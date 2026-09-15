/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Workspace.Separation.Keys

/-!
# Third-coordinate physical separation
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical
namespace LatticeNearestPlaneScratchWorkspaceSeparation

open Execution
open ClassicalRoutines.NumberTheory

noncomputable section

/-- Unified physical cell underlying one third-phase semantic cell. -/
def thirdCell : LatticeNearestPlaneThird.PhaseCell → PhysicalCell
  | .basisFirstFirst => .inl .basis11
  | .basisFirstSecond => .inl .basis12
  | .basisFirstThird => .inl .basis13
  | .basisSecondFirst => .inl .basis21
  | .basisSecondSecond => .inl .basis22
  | .basisSecondThird => .inl .basis23
  | .basisThirdFirst => .inl .basis31
  | .basisThirdSecond => .inl .basis32
  | .basisThirdThird => .inl .basis33
  | .targetFirst => .inl .targetFirst
  | .targetSecond => .inl .targetSecond
  | .targetThird => .inl .targetThird
  | .crossFirst => .inr .crossFirst
  | .crossSecond => .inr .crossSecond
  | .crossThird => .inr .crossThird
  | .productLeft => .inr .crossProductLeft
  | .productRight => .inr .crossProductRight
  | .dotProduct => .inr .dotProduct
  | .numerator => .inr .numerator
  | .denominator => .inr .denominator
  | .denominatorMagnitude => .inr .g11
  | .divisionMagnitude => .inr .divisionMagnitude
  | .divisionNegative => .inr .divisionNegative
  | .divisionWideNumerator => .inr .divisionWideNumerator
  | .divisionWideDenominator => .inr .divisionWideDenominator
  | .divisionQuotientRemainder => .inr .divisionQuotientRemainder
  | .divisionOutput => .inr .thirdOutput
  | .reduceProduct => .inr .reduceProduct

private def thirdCellInverse : PhysicalCell →
    Option LatticeNearestPlaneThird.PhaseCell
  | .inl .basis11 => some .basisFirstFirst
  | .inl .basis12 => some .basisFirstSecond
  | .inl .basis13 => some .basisFirstThird
  | .inl .basis21 => some .basisSecondFirst
  | .inl .basis22 => some .basisSecondSecond
  | .inl .basis23 => some .basisSecondThird
  | .inl .basis31 => some .basisThirdFirst
  | .inl .basis32 => some .basisThirdSecond
  | .inl .basis33 => some .basisThirdThird
  | .inl .targetFirst => some .targetFirst
  | .inl .targetSecond => some .targetSecond
  | .inl .targetThird => some .targetThird
  | .inr .crossFirst => some .crossFirst
  | .inr .crossSecond => some .crossSecond
  | .inr .crossThird => some .crossThird
  | .inr .crossProductLeft => some .productLeft
  | .inr .crossProductRight => some .productRight
  | .inr .dotProduct => some .dotProduct
  | .inr .numerator => some .numerator
  | .inr .denominator => some .denominator
  | .inr .g11 => some .denominatorMagnitude
  | .inr .divisionMagnitude => some .divisionMagnitude
  | .inr .divisionNegative => some .divisionNegative
  | .inr .divisionWideNumerator => some .divisionWideNumerator
  | .inr .divisionWideDenominator => some .divisionWideDenominator
  | .inr .divisionQuotientRemainder => some .divisionQuotientRemainder
  | .inr .thirdOutput => some .divisionOutput
  | .inr .reduceProduct => some .reduceProduct
  | _ => none

private theorem thirdCellInverse_apply
    (cell : LatticeNearestPlaneThird.PhaseCell) :
    thirdCellInverse (thirdCell cell) = some cell := by
  cases cell <;> rfl

/-- The third-phase semantic projection is injective. -/
theorem thirdCell_injective : Function.Injective thirdCell := by
  intro left right equal
  have mapped := congrArg thirdCellInverse equal
  rw [thirdCellInverse_apply, thirdCellInverse_apply] at mapped
  exact Option.some.inj mapped

/-- Third-phase semantic keys are their unified physical keys. -/
theorem thirdCellKey_eq_physicalKey {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N)
    (cell : LatticeNearestPlaneThird.PhaseCell) :
    LatticeNearestPlaneThird.phaseCellKey
        (LatticeNearestPlaneThree.thirdRefs
          (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs state scratch)) cell =
      physicalKey state scratch (thirdCell cell) := by
  cases cell <;> rfl

/-- Physical packages supply the third-phase global key separation. -/
theorem thirdPhaseSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    LatticeNearestPlaneThird.PhaseSeparation
      (LatticeNearestPlaneThree.thirdRefs
        (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
          state scratch)) := by
  refine ⟨?_⟩
  intro left right equal
  apply thirdCell_injective
  apply physicalKey_injective certificates
  simpa only [thirdCellKey_eq_physicalKey] using equal

private def thirdCrossMutableCell : LatticeCross.MutableCell →
    LatticeNearestPlaneThird.PhaseCell
  | .outputFirst => .crossFirst
  | .outputSecond => .crossSecond
  | .outputThird => .crossThird
  | .productLeft => .productLeft
  | .productRight => .productRight

private theorem thirdCrossMutableCell_injective :
    Function.Injective thirdCrossMutableCell := by
  intro left right equal
  cases left <;> cases right <;> cases equal <;> rfl

private theorem thirdCrossMutableKey {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeNearestPlaneThird.Refs ctx width)
    (cell : LatticeCross.MutableCell) :
    LatticeCross.mutableKey refs.cross refs.productLeft refs.productRight cell =
      LatticeNearestPlaneThird.phaseCellKey refs (thirdCrossMutableCell cell) := by
  cases cell <;> rfl

private def thirdCrossSourceCell : LatticeCross.SourceCell →
    LatticeNearestPlaneThird.PhaseCell
  | .leftFirst => .basisFirstFirst
  | .leftSecond => .basisFirstSecond
  | .leftThird => .basisFirstThird
  | .rightFirst => .basisSecondFirst
  | .rightSecond => .basisSecondSecond
  | .rightThird => .basisSecondThird

/-- Physical phase separation supplies the complete third-coordinate cross
product subcontract. -/
theorem thirdCrossSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeNearestPlaneThree.thirdRefs
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
    LatticeCross.PointCrossSeparation refs.basis.first refs.basis.second
      refs.cross refs.productLeft refs.productRight := by
  let refs := LatticeNearestPlaneThree.thirdRefs
    (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
      state scratch)
  change LatticeCross.PointCrossSeparation refs.basis.first refs.basis.second
    refs.cross refs.productLeft refs.productRight
  have phase : LatticeNearestPlaneThird.PhaseSeparation refs :=
    thirdPhaseSeparation certificates
  refine {
    sourceAvoidsMutable := ?_
    mutableInjective := ?_ }
  · intro source target
    have keyNe := phase.phaseCellKey_ne (thirdCrossSourceCell source)
      (thirdCrossMutableCell target) (by
        cases source <;> cases target <;> decide)
    cases source <;> cases target <;>
      apply storageRead_not_mem <;> exact keyNe
  · intro left right equal
    apply thirdCrossMutableCell_injective
    apply phase.keyInjective
    simpa only [thirdCrossMutableKey] using equal

private theorem thirdWriteInputAvoids {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} {shape : CShape}
    (refs : LatticeNearestPlaneThird.Refs ctx width)
    (phase : LatticeNearestPlaneThird.PhaseSeparation refs)
    (source : CWriteRef ctx shape)
    (sourceCell target : LatticeNearestPlaneThird.PhaseCell)
    (sourceKey : source.toCStorageRef.key =
      LatticeNearestPlaneThird.phaseCellKey refs sourceCell)
    (different : sourceCell ≠ target) :
    LatticeNearestPlaneThird.phaseCellKey refs target ∉
      (SignedWord.writeInput source).storageKeys := by
  apply storageRead_not_mem
  rw [sourceKey]
  exact phase.phaseCellKey_ne sourceCell target different

private theorem thirdCoordinateInputAvoids {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeNearestPlaneThird.Refs ctx width)
    (phase : LatticeNearestPlaneThird.PhaseSeparation refs)
    (source : CWriteRef ctx (LatticeState.RawSignedWordShape width))
    (sourceCell target : LatticeNearestPlaneThird.PhaseCell)
    (sourceKey : source.toCStorageRef.key =
      LatticeNearestPlaneThird.phaseCellKey refs sourceCell)
    (different : sourceCell ≠ target) :
    LatticeNearestPlaneThird.phaseCellKey refs target ∉
      (LatticeState.coordinateInput source).storageKeys := by
  apply storageRead_not_mem
  rw [sourceKey]
  exact phase.phaseCellKey_ne sourceCell target different

private theorem thirdDotCoordinateSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeNearestPlaneThird.Refs ctx width)
    (phase : LatticeNearestPlaneThird.PhaseSeparation refs)
    (left right accumulator product :
      CWriteRef ctx (LatticeState.RawSignedWordShape width))
    (leftCell rightCell accumulatorCell productCell :
      LatticeNearestPlaneThird.PhaseCell)
    (leftKey : left.toCStorageRef.key =
      LatticeNearestPlaneThird.phaseCellKey refs leftCell)
    (rightKey : right.toCStorageRef.key =
      LatticeNearestPlaneThird.phaseCellKey refs rightCell)
    (accumulatorKey : accumulator.toCStorageRef.key =
      LatticeNearestPlaneThird.phaseCellKey refs accumulatorCell)
    (productKey : product.toCStorageRef.key =
      LatticeNearestPlaneThird.phaseCellKey refs productCell)
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
    exact thirdCoordinateInputAvoids refs phase left leftCell productCell
      leftKey leftNeProduct
  · rw [productKey]
    exact thirdCoordinateInputAvoids refs phase right rightCell productCell
      rightKey rightNeProduct
  · rw [productKey]
    exact thirdWriteInputAvoids refs phase accumulator accumulatorCell productCell
      accumulatorKey accumulatorNeProduct
  · rw [accumulatorKey]
    exact thirdCoordinateInputAvoids refs phase left leftCell accumulatorCell
      leftKey leftNeAccumulator
  · rw [accumulatorKey]
    exact thirdCoordinateInputAvoids refs phase right rightCell accumulatorCell
      rightKey rightNeAccumulator
  · rw [accumulatorKey]
    exact thirdWriteInputAvoids refs phase product productCell accumulatorCell
      productKey productNeAccumulator

/-- Physical phase separation supplies the refreshed third-coordinate
numerator dot product. -/
theorem thirdNumeratorDotSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeNearestPlaneThree.thirdRefs
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
    LatticeDotRefresh.Separation refs.target refs.cross
      (LatticeNearestPlaneThird.numeratorDotRefs refs) := by
  let refs := LatticeNearestPlaneThree.thirdRefs
    (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
      state scratch)
  change LatticeDotRefresh.Separation refs.target refs.cross
    (LatticeNearestPlaneThird.numeratorDotRefs refs)
  have phase : LatticeNearestPlaneThird.PhaseSeparation refs :=
    thirdPhaseSeparation certificates
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · exact thirdDotCoordinateSeparation refs phase refs.target.first
      refs.cross.first refs.numerator refs.dotProduct .targetFirst .crossFirst
      .numerator .dotProduct rfl rfl rfl rfl (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
  · exact thirdDotCoordinateSeparation refs phase refs.target.second
      refs.cross.second refs.numerator refs.dotProduct .targetSecond .crossSecond
      .numerator .dotProduct rfl rfl rfl rfl (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
  · exact thirdDotCoordinateSeparation refs phase refs.target.third
      refs.cross.third refs.numerator refs.dotProduct .targetThird .crossThird
      .numerator .dotProduct rfl rfl rfl rfl (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)

/-- Physical phase separation supplies the refreshed signed third-coordinate
denominator dot product. -/
theorem thirdDenominatorDotSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeNearestPlaneThree.thirdRefs
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
    LatticeDotRefresh.Separation refs.basis.third refs.cross
      (LatticeNearestPlaneThird.denominatorDotRefs refs) := by
  let refs := LatticeNearestPlaneThree.thirdRefs
    (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
      state scratch)
  change LatticeDotRefresh.Separation refs.basis.third refs.cross
    (LatticeNearestPlaneThird.denominatorDotRefs refs)
  have phase : LatticeNearestPlaneThird.PhaseSeparation refs :=
    thirdPhaseSeparation certificates
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · exact thirdDotCoordinateSeparation refs phase refs.basis.third.first
      refs.cross.first refs.denominator refs.dotProduct .basisThirdFirst .crossFirst
      .denominator .dotProduct rfl rfl rfl rfl (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
  · exact thirdDotCoordinateSeparation refs phase refs.basis.third.second
      refs.cross.second refs.denominator refs.dotProduct .basisThirdSecond .crossSecond
      .denominator .dotProduct rfl rfl rfl rfl (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
  · exact thirdDotCoordinateSeparation refs phase refs.basis.third.third
      refs.cross.third refs.denominator refs.dotProduct .basisThirdThird .crossThird
      .denominator .dotProduct rfl rfl rfl rfl (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)

/-- Physical phase separation supplies the third-coordinate rounded-division
subcontract. -/
theorem thirdDivisionSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeNearestPlaneThree.thirdRefs
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
    SignedWord.RoundedDiv.Separation refs.division := by
  let refs := LatticeNearestPlaneThree.thirdRefs
    (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
      state scratch)
  change SignedWord.RoundedDiv.Separation refs.division
  have phase : LatticeNearestPlaneThird.PhaseSeparation refs :=
    thirdPhaseSeparation certificates
  have numeratorAvoids (target : LatticeNearestPlaneThird.PhaseCell)
      (different : LatticeNearestPlaneThird.PhaseCell.numerator ≠ target) :
      LatticeNearestPlaneThird.phaseCellKey refs target ∉
        refs.division.numerator.storageKeys := by
    rw [refs.divisionNumerator]
    exact thirdWriteInputAvoids refs phase refs.numerator .numerator target rfl
      different
  have denominatorAvoids (target : LatticeNearestPlaneThird.PhaseCell)
      (different :
        LatticeNearestPlaneThird.PhaseCell.denominatorMagnitude ≠ target) :
      LatticeNearestPlaneThird.phaseCellKey refs target ∉
        refs.division.denominator.storageKeys := by
    rw [refs.divisionDenominator]
    exact thirdWriteInputAvoids refs phase refs.denominatorMagnitude
      .denominatorMagnitude target rfl different
  have divisionKeyNe (left right : LatticeNearestPlaneThird.PhaseCell)
      (different : left ≠ right) :
      LatticeNearestPlaneThird.phaseCellKey refs left ≠
        LatticeNearestPlaneThird.phaseCellKey refs right :=
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

private theorem thirdCoordinateAvoidsWrite {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeNearestPlaneThird.Refs ctx width)
    (phase : LatticeNearestPlaneThird.PhaseSeparation refs)
    (source target : CWriteRef ctx (LatticeState.RawSignedWordShape width))
    (sourceCell targetCell : LatticeNearestPlaneThird.PhaseCell)
    (sourceKey : source.toCStorageRef.key =
      LatticeNearestPlaneThird.phaseCellKey refs sourceCell)
    (targetKey : target.toCStorageRef.key =
      LatticeNearestPlaneThird.phaseCellKey refs targetCell)
    (different : sourceCell ≠ targetCell) :
    target.toCStorageRef.key ∉ (LatticeState.coordinateInput source).storageKeys := by
  rw [targetKey]
  exact thirdCoordinateInputAvoids refs phase source sourceCell targetCell
    sourceKey different

private theorem thirdWriteInputAvoidsWrite {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeNearestPlaneThird.Refs ctx width)
    (phase : LatticeNearestPlaneThird.PhaseSeparation refs)
    (source target : CWriteRef ctx (LatticeState.RawSignedWordShape width))
    (sourceCell targetCell : LatticeNearestPlaneThird.PhaseCell)
    (sourceKey : source.toCStorageRef.key =
      LatticeNearestPlaneThird.phaseCellKey refs sourceCell)
    (targetKey : target.toCStorageRef.key =
      LatticeNearestPlaneThird.phaseCellKey refs targetCell)
    (different : sourceCell ≠ targetCell) :
    target.toCStorageRef.key ∉ (SignedWord.writeInput source).storageKeys := by
  rw [targetKey]
  exact thirdWriteInputAvoids refs phase source sourceCell targetCell sourceKey
    different

private theorem thirdReduceCoordinateSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeNearestPlaneThird.Refs ctx width)
    (phase : LatticeNearestPlaneThird.PhaseSeparation refs)
    (source target : CWriteRef ctx (LatticeState.RawSignedWordShape width))
    (sourceCell targetCell : LatticeNearestPlaneThird.PhaseCell)
    (sourceKey : source.toCStorageRef.key =
      LatticeNearestPlaneThird.phaseCellKey refs sourceCell)
    (targetKey : target.toCStorageRef.key =
      LatticeNearestPlaneThird.phaseCellKey refs targetCell)
    (sourceNeProduct : sourceCell ≠ .reduceProduct)
    (targetNeProduct : targetCell ≠ .reduceProduct)
    (coefficientNeTarget :
      LatticeNearestPlaneThird.PhaseCell.divisionOutput ≠ targetCell)
    (sourceNeTarget : sourceCell ≠ targetCell)
    (productNeTarget :
      LatticeNearestPlaneThird.PhaseCell.reduceProduct ≠ targetCell) :
    LatticeArithmetic.CoordinateReduceSeparation
      (SignedWord.writeInput refs.division.output)
      (LatticeState.coordinateInput source) target refs.reduceProduct := by
  have coefficientKey : refs.division.output.toCStorageRef.key =
      LatticeNearestPlaneThird.phaseCellKey refs .divisionOutput := rfl
  have productKey : refs.reduceProduct.toCStorageRef.key =
      LatticeNearestPlaneThird.phaseCellKey refs .reduceProduct := rfl
  refine {
    coefficientAvoidsProduct := ?_
    sourceAvoidsProduct := ?_
    targetAvoidsProduct := ?_
    coefficientAvoidsTarget := ?_
    sourceAvoidsTarget := ?_
    productAvoidsTarget := ?_ }
  · exact thirdWriteInputAvoidsWrite refs phase refs.division.output
      refs.reduceProduct .divisionOutput .reduceProduct coefficientKey
        productKey (by decide)
  · exact thirdCoordinateAvoidsWrite refs phase source refs.reduceProduct
      sourceCell .reduceProduct sourceKey productKey sourceNeProduct
  · exact thirdWriteInputAvoidsWrite refs phase target refs.reduceProduct
      targetCell .reduceProduct targetKey productKey targetNeProduct
  · exact thirdWriteInputAvoidsWrite refs phase refs.division.output target
      .divisionOutput targetCell coefficientKey targetKey coefficientNeTarget
  · exact thirdCoordinateAvoidsWrite refs phase source target sourceCell
      targetCell sourceKey targetKey sourceNeTarget
  · exact thirdWriteInputAvoidsWrite refs phase refs.reduceProduct target
      .reduceProduct targetCell productKey targetKey productNeTarget

/-- Physical phase separation supplies the third-coordinate point reduction
subcontract. -/
theorem thirdReductionSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeNearestPlaneThree.thirdRefs
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
    LatticeArithmetic.PointReduceSeparation
      (SignedWord.writeInput refs.division.output) refs.basis.third refs.target
        refs.reduceProduct := by
  let refs := LatticeNearestPlaneThree.thirdRefs
    (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
      state scratch)
  change LatticeArithmetic.PointReduceSeparation
    (SignedWord.writeInput refs.division.output) refs.basis.third refs.target
      refs.reduceProduct
  have phase : LatticeNearestPlaneThird.PhaseSeparation refs :=
    thirdPhaseSeparation certificates
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
  · exact thirdReduceCoordinateSeparation refs phase refs.basis.third.first
      refs.target.first .basisThirdFirst .targetFirst rfl rfl (by decide)
        (by decide) (by decide) (by decide) (by decide)
  · exact thirdReduceCoordinateSeparation refs phase refs.basis.third.second
      refs.target.second .basisThirdSecond .targetSecond rfl rfl (by decide)
        (by decide) (by decide) (by decide) (by decide)
  · exact thirdReduceCoordinateSeparation refs phase refs.basis.third.third
      refs.target.third .basisThirdThird .targetThird rfl rfl (by decide)
        (by decide) (by decide) (by decide) (by decide)
  · exact thirdCoordinateAvoidsWrite refs phase refs.basis.third.second
      refs.target.first .basisThirdSecond .targetFirst rfl rfl (by decide)
  · exact thirdCoordinateAvoidsWrite refs phase refs.basis.third.third
      refs.target.first .basisThirdThird .targetFirst rfl rfl (by decide)
  · exact thirdCoordinateAvoidsWrite refs phase refs.basis.third.third
      refs.target.second .basisThirdThird .targetSecond rfl rfl (by decide)
  · exact thirdWriteInputAvoidsWrite refs phase refs.target.first
      refs.target.second .targetFirst .targetSecond rfl rfl (by decide)
  · exact thirdWriteInputAvoidsWrite refs phase refs.target.first
      refs.target.third .targetFirst .targetThird rfl rfl (by decide)
  · exact thirdWriteInputAvoidsWrite refs phase refs.target.second
      refs.target.first .targetSecond .targetFirst rfl rfl (by decide)
  · exact thirdWriteInputAvoidsWrite refs phase refs.target.second
      refs.target.third .targetSecond .targetThird rfl rfl (by decide)
  · exact thirdWriteInputAvoidsWrite refs phase refs.target.third
      refs.target.first .targetThird .targetFirst rfl rfl (by decide)
  · exact thirdWriteInputAvoidsWrite refs phase refs.target.third
      refs.target.second .targetThird .targetSecond rfl rfl (by decide)

/-- The persistent state and reusable scratch package satisfy the complete
third-coordinate separation contract. -/
theorem thirdSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    LatticeNearestPlaneThird.Separation
      (LatticeNearestPlaneThree.thirdRefs
        (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
          state scratch)) := by
  refine {
    phase := thirdPhaseSeparation certificates
    cross := thirdCrossSeparation certificates
    numeratorDot := thirdNumeratorDotSeparation certificates
    denominatorDot := thirdDenominatorDotSeparation certificates
    division := thirdDivisionSeparation certificates
    reduction := thirdReductionSeparation certificates }

end

end LatticeNearestPlaneScratchWorkspaceSeparation
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical
