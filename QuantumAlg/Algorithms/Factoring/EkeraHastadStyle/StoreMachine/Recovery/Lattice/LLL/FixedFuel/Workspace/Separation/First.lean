/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Workspace.Separation.Keys

/-!
# Physical separation for the first LLL phase
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelScratchWorkspaceSeparation

open ClassicalRoutines
open ClassicalRoutines.NumberTheory
open Execution

noncomputable section

/-- First-phase global key separation supplies the complete rounded-division
subcontract. -/
theorem firstDivisionSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    SignedWord.RoundedDiv.Separation
      (LatticeFixedFuelScratchWorkspaceViews.firstDivisionRefs scratch) := by
  let refs := LatticeFixedFuelScratchWorkspaceViews.firstRefs
    state scratch
  have phase : LatticeFirstPairMachine.PhaseSeparation refs :=
    firstPhaseSeparation certificates
  have numeratorAvoids (target : LatticeFirstPairMachine.TransitionCell)
      (different : .g21 ≠ target) :
      (LatticeFirstPairMachine.cellKey refs target) ∉
        refs.division.numerator.storageKeys := by
    simpa only [refs, LatticeFixedFuelScratchWorkspaceViews.firstRefs,
      LatticeFixedFuelScratchWorkspaceViews.firstDivisionRefs,
      LatticeFixedFuelScratchWorkspaceViews.metricRefs,
      SignedWord.writeInput,
      CInputRef.storageKeys, List.mem_singleton, ne_comm, LatticeFirstPairMachine.cellKey] using
      phase.cellKey_ne .g21 target different
  have denominatorAvoids (target : LatticeFirstPairMachine.TransitionCell)
      (different : .g11 ≠ target) :
      (LatticeFirstPairMachine.cellKey refs target) ∉
        refs.division.denominator.storageKeys := by
    simpa only [refs, LatticeFixedFuelScratchWorkspaceViews.firstRefs,
      LatticeFixedFuelScratchWorkspaceViews.firstDivisionRefs,
      LatticeFixedFuelScratchWorkspaceViews.metricRefs,
      SignedWord.writeInput,
      CInputRef.storageKeys, List.mem_singleton, ne_comm, LatticeFirstPairMachine.cellKey] using
      phase.cellKey_ne .g11 target different
  have divisionKeyNe (left right : LatticeFirstPairMachine.TransitionCell)
      (different : left ≠ right) :
      LatticeFirstPairMachine.cellKey refs left ≠
        LatticeFirstPairMachine.cellKey refs right :=
    phase.cellKey_ne left right different
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
  all_goals
    simp only [LatticeFixedFuelScratchWorkspaceViews.firstDivisionRefs]
  · exact numeratorAvoids .magnitude (by decide)
  · exact numeratorAvoids .negative (by decide)
  · exact numeratorAvoids .wideNumerator (by decide)
  · exact numeratorAvoids .wideDenominator (by decide)
  · exact numeratorAvoids .division (by decide)
  · exact numeratorAvoids .coefficient (by decide)
  · exact denominatorAvoids .magnitude (by decide)
  · exact denominatorAvoids .negative (by decide)
  · exact denominatorAvoids .wideNumerator (by decide)
  · exact denominatorAvoids .wideDenominator (by decide)
  · exact denominatorAvoids .division (by decide)
  · exact denominatorAvoids .coefficient (by decide)
  · exact divisionKeyNe .magnitude .negative (by decide)
  · exact divisionKeyNe .magnitude .wideNumerator (by decide)
  · exact divisionKeyNe .magnitude .wideDenominator (by decide)
  · exact divisionKeyNe .magnitude .division (by decide)
  · exact divisionKeyNe .magnitude .coefficient (by decide)
  · exact divisionKeyNe .negative .wideNumerator (by decide)
  · exact divisionKeyNe .negative .wideDenominator (by decide)
  · exact divisionKeyNe .negative .division (by decide)
  · exact divisionKeyNe .negative .coefficient (by decide)
  · exact divisionKeyNe .wideNumerator .wideDenominator (by decide)
  · exact divisionKeyNe .wideNumerator .division (by decide)
  · exact divisionKeyNe .wideNumerator .coefficient (by decide)
  · exact divisionKeyNe .wideDenominator .division (by decide)
  · exact divisionKeyNe .wideDenominator .coefficient (by decide)
  · exact divisionKeyNe .division .coefficient (by decide)

/-- First-phase global key separation supplies the three-coordinate reduction
subcontract. -/
theorem firstReductionSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeFixedFuelScratchWorkspaceViews.firstRefs
      state scratch
    LatticeArithmetic.PointReduceSeparation
      (SignedWord.writeInput
        refs.division.output)
      refs.basis.first refs.basis.second refs.reduceProduct := by
  let refs := LatticeFixedFuelScratchWorkspaceViews.firstRefs
    state scratch
  change LatticeArithmetic.PointReduceSeparation
    (SignedWord.writeInput
      refs.division.output)
    refs.basis.first refs.basis.second refs.reduceProduct
  have phase : LatticeFirstPairMachine.PhaseSeparation refs :=
    firstPhaseSeparation certificates
  have writeAvoids {sourceShape targetShape : CShape}
      (source : CWriteRef ctx sourceShape) (target : CWriteRef ctx targetShape)
      (sourceCell targetCell : LatticeFirstPairMachine.TransitionCell)
      (sourceKey : source.toCStorageRef.key =
        LatticeFirstPairMachine.cellKey refs sourceCell)
      (targetKey : target.toCStorageRef.key =
        LatticeFirstPairMachine.cellKey refs targetCell)
      (different : sourceCell ≠ targetCell) :
      target.toCStorageRef.key ∉ (SignedWord.writeInput source).storageKeys := by
    apply storageRead_avoids_of_key_ne
    rw [sourceKey, targetKey]
    exact phase.cellKey_ne sourceCell targetCell different
  have coordinateAvoids
      (source target : CWriteRef ctx (.unsignedWord
        (LatticeFixedFuelScratchWorkspaceLayout.Width N)))
      (sourceCell targetCell : LatticeFirstPairMachine.TransitionCell)
      (sourceKey : source.toCStorageRef.key =
        LatticeFirstPairMachine.cellKey refs sourceCell)
      (targetKey : target.toCStorageRef.key =
        LatticeFirstPairMachine.cellKey refs targetCell)
      (different : sourceCell ≠ targetCell) :
      target.toCStorageRef.key ∉ (LatticeState.coordinateInput source).storageKeys := by
    apply storageRead_avoids_of_key_ne
    change source.toCStorageRef.key ≠ target.toCStorageRef.key
    rw [sourceKey, targetKey]
    exact phase.cellKey_ne sourceCell targetCell different
  have coordinateSeparation
      (source target : CWriteRef ctx (.unsignedWord
        (LatticeFixedFuelScratchWorkspaceLayout.Width N)))
      (sourceCell targetCell : LatticeFirstPairMachine.TransitionCell)
      (sourceKey : source.toCStorageRef.key =
        LatticeFirstPairMachine.cellKey refs sourceCell)
      (targetKey : target.toCStorageRef.key =
        LatticeFirstPairMachine.cellKey refs targetCell)
      (sourceNeProduct : sourceCell ≠ .reduceProduct)
      (targetNeProduct : targetCell ≠ .reduceProduct)
      (coefficientNeTarget : .coefficient ≠ targetCell)
      (sourceNeTarget : sourceCell ≠ targetCell)
      (productNeTarget : .reduceProduct ≠ targetCell) :
      LatticeArithmetic.CoordinateReduceSeparation
        (SignedWord.writeInput
          refs.division.output)
        (LatticeState.coordinateInput source) target refs.reduceProduct := by
    refine {
      coefficientAvoidsProduct := ?_
      sourceAvoidsProduct := ?_
      targetAvoidsProduct := ?_
      coefficientAvoidsTarget := ?_
      sourceAvoidsTarget := ?_
      productAvoidsTarget := ?_ }
    · exact writeAvoids refs.division.output refs.reduceProduct .coefficient
        .reduceProduct rfl rfl (by decide)
    · exact coordinateAvoids source refs.reduceProduct sourceCell .reduceProduct
        sourceKey rfl sourceNeProduct
    · exact writeAvoids target refs.reduceProduct targetCell .reduceProduct
        targetKey rfl targetNeProduct
    · exact writeAvoids refs.division.output target .coefficient targetCell
        rfl targetKey coefficientNeTarget
    · exact coordinateAvoids source target sourceCell targetCell sourceKey targetKey
        sourceNeTarget
    · exact writeAvoids refs.reduceProduct target .reduceProduct targetCell
        rfl targetKey productNeTarget
  refine {
    first := coordinateSeparation refs.basis.first.first refs.basis.second.first
      .b11 .b21 rfl rfl (by decide) (by decide) (by decide) (by decide)
        (by decide)
    second := coordinateSeparation refs.basis.first.second refs.basis.second.second
      .b12 .b22 rfl rfl (by decide) (by decide) (by decide) (by decide)
        (by decide)
    third := coordinateSeparation refs.basis.first.third refs.basis.second.third
      .b13 .b23 rfl rfl (by decide) (by decide) (by decide) (by decide)
        (by decide)
    sourceSecondAvoidsFirstTarget := ?_
    sourceThirdAvoidsFirstTarget := ?_
    sourceThirdAvoidsSecondTarget := ?_
    targetFirstAvoidsSecond := ?_
    targetFirstAvoidsThird := ?_
    targetSecondAvoidsFirst := ?_
    targetSecondAvoidsThird := ?_
    targetThirdAvoidsFirst := ?_
    targetThirdAvoidsSecond := ?_ }
  · exact coordinateAvoids refs.basis.first.second refs.basis.second.first
      .b12 .b21 rfl rfl (by decide)
  · exact coordinateAvoids refs.basis.first.third refs.basis.second.first
      .b13 .b21 rfl rfl (by decide)
  · exact coordinateAvoids refs.basis.first.third refs.basis.second.second
      .b13 .b22 rfl rfl (by decide)
  · exact writeAvoids refs.basis.second.first refs.basis.second.second
      .b21 .b22 rfl rfl (by decide)
  · exact writeAvoids refs.basis.second.first refs.basis.second.third
      .b21 .b23 rfl rfl (by decide)
  · exact writeAvoids refs.basis.second.second refs.basis.second.first
      .b22 .b21 rfl rfl (by decide)
  · exact writeAvoids refs.basis.second.second refs.basis.second.third
      .b22 .b23 rfl rfl (by decide)
  · exact writeAvoids refs.basis.second.third refs.basis.second.first
      .b23 .b21 rfl rfl (by decide)
  · exact writeAvoids refs.basis.second.third refs.basis.second.second
      .b23 .b22 rfl rfl (by decide)

/-- First-phase global key separation supplies the norm-refresh subcontract. -/
theorem firstRefreshSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeFixedFuelScratchWorkspaceViews.firstRefs
      state scratch
    LatticeNormRefresh.Separation refs.basis.second refs.refresh := by
  let refs := LatticeFixedFuelScratchWorkspaceViews.firstRefs
    state scratch
  change LatticeNormRefresh.Separation refs.basis.second refs.refresh
  have phase : LatticeFirstPairMachine.PhaseSeparation refs :=
    firstPhaseSeparation certificates
  have writeAvoids {sourceShape targetShape : CShape}
      (source : CWriteRef ctx sourceShape) (target : CWriteRef ctx targetShape)
      (sourceCell targetCell : LatticeFirstPairMachine.TransitionCell)
      (sourceKey : source.toCStorageRef.key =
        LatticeFirstPairMachine.cellKey refs sourceCell)
      (targetKey : target.toCStorageRef.key =
        LatticeFirstPairMachine.cellKey refs targetCell)
      (different : sourceCell ≠ targetCell) :
      target.toCStorageRef.key ∉ (SignedWord.writeInput source).storageKeys := by
    apply storageRead_avoids_of_key_ne
    rw [sourceKey, targetKey]
    exact phase.cellKey_ne sourceCell targetCell different
  have coordinateAvoids
      (source target : CWriteRef ctx (.unsignedWord
        (LatticeFixedFuelScratchWorkspaceLayout.Width N)))
      (sourceCell targetCell : LatticeFirstPairMachine.TransitionCell)
      (sourceKey : source.toCStorageRef.key =
        LatticeFirstPairMachine.cellKey refs sourceCell)
      (targetKey : target.toCStorageRef.key =
        LatticeFirstPairMachine.cellKey refs targetCell)
      (different : sourceCell ≠ targetCell) :
      target.toCStorageRef.key ∉ (LatticeState.coordinateInput source).storageKeys := by
    apply storageRead_avoids_of_key_ne
    change source.toCStorageRef.key ≠ target.toCStorageRef.key
    rw [sourceKey, targetKey]
    exact phase.cellKey_ne sourceCell targetCell different
  have coordinateSeparation
      (source : CWriteRef ctx (.unsignedWord
        (LatticeFixedFuelScratchWorkspaceLayout.Width N)))
      (sourceCell : LatticeFirstPairMachine.TransitionCell)
      (sourceKey : source.toCStorageRef.key =
        LatticeFirstPairMachine.cellKey refs sourceCell)
      (sourceNeProduct : sourceCell ≠ .refreshProduct)
      (sourceNeAccumulator : sourceCell ≠ .g22) :
      LatticeDot.CoordinateAccumulateSeparation
        (LatticeState.coordinateInput source)
        (LatticeState.coordinateInput source) refs.refresh.norm
        refs.refresh.product := by
    refine {
      leftAvoidsProduct := ?_
      rightAvoidsProduct := ?_
      accumulatorAvoidsProduct := ?_
      leftAvoidsAccumulator := ?_
      rightAvoidsAccumulator := ?_
      productAvoidsAccumulator := ?_ }
    · exact coordinateAvoids source refs.refresh.product sourceCell .refreshProduct
        sourceKey rfl sourceNeProduct
    · exact coordinateAvoids source refs.refresh.product sourceCell .refreshProduct
        sourceKey rfl sourceNeProduct
    · exact writeAvoids refs.refresh.norm refs.refresh.product .g22 .refreshProduct
        rfl rfl (by decide)
    · exact coordinateAvoids source refs.refresh.norm sourceCell .g22
        sourceKey rfl sourceNeAccumulator
    · exact coordinateAvoids source refs.refresh.norm sourceCell .g22
        sourceKey rfl sourceNeAccumulator
    · exact writeAvoids refs.refresh.product refs.refresh.norm .refreshProduct .g22
        rfl rfl (by decide)
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · exact coordinateSeparation refs.basis.second.first .b21 rfl
      (by decide) (by decide)
  · exact coordinateSeparation refs.basis.second.second .b22 rfl
      (by decide) (by decide)
  · exact coordinateSeparation refs.basis.second.third .b23 rfl
      (by decide) (by decide)

/-- First-phase global key separation supplies the Lovasz-decision
subcontract. -/
theorem firstLovaszSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeFixedFuelScratchWorkspaceViews.firstRefs
      state scratch
    LatticeLovasz.FirstLovaszSeparation refs.metric refs.lovasz := by
  let refs := LatticeFixedFuelScratchWorkspaceViews.firstRefs
    state scratch
  change LatticeLovasz.FirstLovaszSeparation refs.metric refs.lovasz
  have phase : LatticeFirstPairMachine.PhaseSeparation refs :=
    firstPhaseSeparation certificates
  refine {
    metricKeyInjective := ?_
    metricAvoidsPass := ?_ }
  · exact (metricSeparation certificates).keyInjective
  · intro cell
    have keyNe := phase.cellKey_ne
      (LatticeFirstPairMachine.metricTransitionCell cell) .passes (by
        cases cell <;> decide)
    cases cell <;>
      simpa only [LatticeMetricMachine.metricCellRef,
        SignedWord.writeInput,
          CInputRef.storageKeys, List.mem_singleton,
            ne_comm, LatticeFirstPairMachine.metricTransitionCell,
        LatticeFirstPairMachine.cellKey] using keyNe

/-- Embed the seven first-row/second-row swap cells into the first-phase key
space. -/
private def firstSwapTransitionCell : LatticeSwap.PointSwapCell →
    LatticeFirstPairMachine.TransitionCell
  | .leftFirst => .b11
  | .leftSecond => .b12
  | .leftThird => .b13
  | .rightFirst => .b21
  | .rightSecond => .b22
  | .rightThird => .b23
  | .scratch => .swapScratch

private theorem firstSwapTransitionCell_injective :
    Function.Injective firstSwapTransitionCell := by
  intro left right equal
  cases left <;> cases right <;> simp [firstSwapTransitionCell] at equal ⊢

/-- First-phase global key separation supplies the point-swap subcontract. -/
theorem firstSwapSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeFixedFuelScratchWorkspaceViews.firstRefs
      state scratch
    LatticeSwap.PointSwapSeparation refs.basis.first refs.basis.second
      refs.swapScratch := by
  let refs := LatticeFixedFuelScratchWorkspaceViews.firstRefs
    state scratch
  change LatticeSwap.PointSwapSeparation refs.basis.first refs.basis.second
    refs.swapScratch
  have phase : LatticeFirstPairMachine.PhaseSeparation refs :=
    firstPhaseSeparation certificates
  refine ⟨?_⟩
  intro left right equal
  apply firstSwapTransitionCell_injective
  apply phase.keyInjective
  cases left <;> cases right <;> exact equal

/-- The physical state and reusable scratch packages satisfy the complete
first-pair semantic separation contract. -/
theorem firstSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    LatticeFirstPairMachine.Separation
      (LatticeFixedFuelScratchWorkspaceViews.firstRefs
        state scratch) := by
  refine {
    phase := firstPhaseSeparation certificates
    division := firstDivisionSeparation certificates
    reduction := firstReductionSeparation certificates
    refresh := firstRefreshSeparation certificates
    lovasz := firstLovaszSeparation certificates
    swap := firstSwapSeparation certificates }

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelScratchWorkspaceSeparation
