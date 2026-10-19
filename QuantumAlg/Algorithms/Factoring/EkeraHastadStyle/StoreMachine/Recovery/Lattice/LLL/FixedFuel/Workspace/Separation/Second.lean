/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Workspace.Separation.First

/-!
# Physical separation for the second LLL phase
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelScratchWorkspaceSeparation

open ClassicalRoutines
open ClassicalRoutines.NumberTheory
open Execution

noncomputable section

/-- Second-prefix global key separation supplies the `mu32` rounded-division
subcontract. -/
lemma secondDivision32Separation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs
      state scratch
    SignedWord.RoundedDiv.Separation
      refs.division32 := by
  let refs := LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs
    state scratch
  change SignedWord.RoundedDiv.Separation
    refs.division32
  have phase : LatticeSecondPairMachine.PhaseSeparation refs :=
    secondPhaseSeparation certificates
  have numeratorAvoids (target : LatticeSecondPairMachine.DivisionCell)
      (different : LatticeSecondPairMachine.TransitionCell.nu32 ≠
        .division32 target) :
      (LatticeSecondPairMachine.cellKey refs (.division32 target)) ∉
        (refs.division32.numerator).storageKeys := by
    simpa only [refs, LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs,
      LatticeFixedFuelScratchWorkspaceViews.division32Refs,
      LatticeFixedFuelScratchWorkspaceViews.reductionInputRefs,
      SignedWord.writeInput,
      CInputRef.storageKeys, List.mem_singleton, ne_comm, LatticeSecondPairMachine.cellKey] using
      phase.cellKey_ne .nu32 (.division32 target) different
  have denominatorAvoids (target : LatticeSecondPairMachine.DivisionCell)
      (different : LatticeSecondPairMachine.TransitionCell.d32 ≠
        .division32 target) :
      (LatticeSecondPairMachine.cellKey refs (.division32 target)) ∉
        (refs.division32.denominator).storageKeys := by
    simpa only [refs, LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs,
      LatticeFixedFuelScratchWorkspaceViews.division32Refs,
      LatticeFixedFuelScratchWorkspaceViews.reductionInputRefs,
      SignedWord.writeInput,
      CInputRef.storageKeys, List.mem_singleton, ne_comm, LatticeSecondPairMachine.cellKey] using
      phase.cellKey_ne .d32 (.division32 target) different
  have divisionKeyNe (left right : LatticeSecondPairMachine.DivisionCell)
      (different : left ≠ right) :
      LatticeSecondPairMachine.cellKey refs (.division32 left) ≠
        LatticeSecondPairMachine.cellKey refs (.division32 right) :=
    phase.cellKey_ne (.division32 left) (.division32 right) (by
      intro equal
      exact different (LatticeSecondPairMachine.TransitionCell.division32.inj equal))
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
  · exact numeratorAvoids .magnitude (by decide)
  · exact numeratorAvoids .negative (by decide)
  · exact numeratorAvoids .wideNumerator (by decide)
  · exact numeratorAvoids .wideDenominator (by decide)
  · exact numeratorAvoids .division (by decide)
  · exact numeratorAvoids .output (by decide)
  · exact denominatorAvoids .magnitude (by decide)
  · exact denominatorAvoids .negative (by decide)
  · exact denominatorAvoids .wideNumerator (by decide)
  · exact denominatorAvoids .wideDenominator (by decide)
  · exact denominatorAvoids .division (by decide)
  · exact denominatorAvoids .output (by decide)
  · exact divisionKeyNe .magnitude .negative (by decide)
  · exact divisionKeyNe .magnitude .wideNumerator (by decide)
  · exact divisionKeyNe .magnitude .wideDenominator (by decide)
  · exact divisionKeyNe .magnitude .division (by decide)
  · exact divisionKeyNe .magnitude .output (by decide)
  · exact divisionKeyNe .negative .wideNumerator (by decide)
  · exact divisionKeyNe .negative .wideDenominator (by decide)
  · exact divisionKeyNe .negative .division (by decide)
  · exact divisionKeyNe .negative .output (by decide)
  · exact divisionKeyNe .wideNumerator .wideDenominator (by decide)
  · exact divisionKeyNe .wideNumerator .division (by decide)
  · exact divisionKeyNe .wideNumerator .output (by decide)
  · exact divisionKeyNe .wideDenominator .division (by decide)
  · exact divisionKeyNe .wideDenominator .output (by decide)
  · exact divisionKeyNe .division .output (by decide)

/-- Second-prefix global key separation supplies the `mu31` rounded-division
subcontract. -/
lemma secondDivision31Separation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs
      state scratch
    SignedWord.RoundedDiv.Separation
      refs.division31 := by
  let refs := LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs
    state scratch
  change SignedWord.RoundedDiv.Separation
    refs.division31
  have phase : LatticeSecondPairMachine.PhaseSeparation refs :=
    secondPhaseSeparation certificates
  have numeratorAvoids (target : LatticeSecondPairMachine.DivisionCell)
      (different : LatticeSecondPairMachine.TransitionCell.g31 ≠
        .division31 target) :
      (LatticeSecondPairMachine.cellKey refs (.division31 target)) ∉
        (refs.division31.numerator).storageKeys := by
    simpa only [refs, LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs,
      LatticeFixedFuelScratchWorkspaceViews.division31Refs,
      LatticeFixedFuelScratchWorkspaceViews.metricRefs,
      SignedWord.writeInput,
      CInputRef.storageKeys, List.mem_singleton, ne_comm, LatticeSecondPairMachine.cellKey] using
      phase.cellKey_ne .g31 (.division31 target) different
  have denominatorAvoids (target : LatticeSecondPairMachine.DivisionCell)
      (different : LatticeSecondPairMachine.TransitionCell.g11 ≠
        .division31 target) :
      (LatticeSecondPairMachine.cellKey refs (.division31 target)) ∉
        (refs.division31.denominator).storageKeys := by
    simpa only [refs, LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs,
      LatticeFixedFuelScratchWorkspaceViews.division31Refs,
      LatticeFixedFuelScratchWorkspaceViews.metricRefs,
      SignedWord.writeInput,
      CInputRef.storageKeys, List.mem_singleton, ne_comm, LatticeSecondPairMachine.cellKey] using
      phase.cellKey_ne .g11 (.division31 target) different
  have divisionKeyNe (left right : LatticeSecondPairMachine.DivisionCell)
      (different : left ≠ right) :
      LatticeSecondPairMachine.cellKey refs (.division31 left) ≠
        LatticeSecondPairMachine.cellKey refs (.division31 right) :=
    phase.cellKey_ne (.division31 left) (.division31 right) (by
      intro equal
      exact different (LatticeSecondPairMachine.TransitionCell.division31.inj equal))
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
  · exact numeratorAvoids .magnitude (by decide)
  · exact numeratorAvoids .negative (by decide)
  · exact numeratorAvoids .wideNumerator (by decide)
  · exact numeratorAvoids .wideDenominator (by decide)
  · exact numeratorAvoids .division (by decide)
  · exact numeratorAvoids .output (by decide)
  · exact denominatorAvoids .magnitude (by decide)
  · exact denominatorAvoids .negative (by decide)
  · exact denominatorAvoids .wideNumerator (by decide)
  · exact denominatorAvoids .wideDenominator (by decide)
  · exact denominatorAvoids .division (by decide)
  · exact denominatorAvoids .output (by decide)
  · exact divisionKeyNe .magnitude .negative (by decide)
  · exact divisionKeyNe .magnitude .wideNumerator (by decide)
  · exact divisionKeyNe .magnitude .wideDenominator (by decide)
  · exact divisionKeyNe .magnitude .division (by decide)
  · exact divisionKeyNe .magnitude .output (by decide)
  · exact divisionKeyNe .negative .wideNumerator (by decide)
  · exact divisionKeyNe .negative .wideDenominator (by decide)
  · exact divisionKeyNe .negative .division (by decide)
  · exact divisionKeyNe .negative .output (by decide)
  · exact divisionKeyNe .wideNumerator .wideDenominator (by decide)
  · exact divisionKeyNe .wideNumerator .division (by decide)
  · exact divisionKeyNe .wideNumerator .output (by decide)
  · exact divisionKeyNe .wideDenominator .division (by decide)
  · exact divisionKeyNe .wideDenominator .output (by decide)
  · exact divisionKeyNe .division .output (by decide)

private lemma secondBasisInputAvoids {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeSecondPairMachine.Refs ctx width)
    (phase : LatticeSecondPairMachine.PhaseSeparation refs)
    (source : LatticeMetricMachine.BasisCell)
    (target : LatticeSecondPairMachine.TransitionCell)
    (different : LatticeSecondPairMachine.basisTransitionCell source ≠ target) :
    (LatticeSecondPairMachine.cellKey refs target) ∉
      (LatticeMetricMachine.basisCellInput refs.basis source).storageKeys := by
  have keyNe := phase.cellKey_ne
    (LatticeSecondPairMachine.basisTransitionCell source) target different
  cases source <;>
    simpa only [LatticeMetricMachine.basisCellInput, LatticeState.coordinateInput,
      CInputRef.storageKeys, List.mem_singleton,
        ne_comm, LatticeSecondPairMachine.basisTransitionCell,
      LatticeSecondPairMachine.cellKey] using keyNe

private lemma secondWriteInputAvoids {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} {shape : CShape}
    (refs : LatticeSecondPairMachine.Refs ctx width)
    (phase : LatticeSecondPairMachine.PhaseSeparation refs)
    (source : CWriteRef ctx shape)
    (sourceCell target : LatticeSecondPairMachine.TransitionCell)
    (sourceKey : source.toCStorageRef.key =
      LatticeSecondPairMachine.cellKey refs sourceCell)
    (different : sourceCell ≠ target) :
    (LatticeSecondPairMachine.cellKey refs target) ∉
      (SignedWord.writeInput source).storageKeys := by
  apply storageRead_avoids_of_key_ne
  rw [sourceKey]
  exact phase.cellKey_ne sourceCell target different

private def secondBasisWriteRef {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (basis : LatticeState.BasisRefs ctx width) :
    LatticeMetricMachine.BasisCell →
      CWriteRef ctx (LatticeState.RawSignedWordShape width)
  | .firstFirst => basis.first.first
  | .firstSecond => basis.first.second
  | .firstThird => basis.first.third
  | .secondFirst => basis.second.first
  | .secondSecond => basis.second.second
  | .secondThird => basis.second.third
  | .thirdFirst => basis.third.first
  | .thirdSecond => basis.third.second
  | .thirdThird => basis.third.third

private lemma secondBasisWriteKey {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeSecondPairMachine.Refs ctx width)
    (cell : LatticeMetricMachine.BasisCell) :
    (secondBasisWriteRef refs.basis cell).toCStorageRef.key =
      LatticeSecondPairMachine.cellKey refs
        (LatticeSecondPairMachine.basisTransitionCell cell) := by
  cases cell <;> rfl

/-- The physical state and scratch packages separate the refreshed `g21`
dot-product phase. -/
lemma secondRefreshG21Separation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs
      state scratch
    LatticeDotRefresh.Separation refs.basis.second refs.basis.first
      (LatticeSecondPairMachine.refreshG21Refs refs) := by
  let refs := LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs
    state scratch
  change LatticeDotRefresh.Separation refs.basis.second refs.basis.first
    (LatticeSecondPairMachine.refreshG21Refs refs)
  have phase : LatticeSecondPairMachine.PhaseSeparation refs :=
    secondPhaseSeparation certificates
  have coordinateSeparation
      (left right : LatticeMetricMachine.BasisCell) :
      LatticeDot.CoordinateAccumulateSeparation
        (LatticeMetricMachine.basisCellInput refs.basis left)
        (LatticeMetricMachine.basisCellInput refs.basis right)
        refs.metric.g21 refs.refreshG21Product := by
    refine {
      leftAvoidsProduct := ?_
      rightAvoidsProduct := ?_
      accumulatorAvoidsProduct := ?_
      leftAvoidsAccumulator := ?_
      rightAvoidsAccumulator := ?_
      productAvoidsAccumulator := ?_ }
    · exact secondBasisInputAvoids refs phase left .refreshG21Product (by
        cases left <;> decide)
    · exact secondBasisInputAvoids refs phase right .refreshG21Product (by
        cases right <;> decide)
    · exact secondWriteInputAvoids refs phase refs.metric.g21 .g21
        .refreshG21Product rfl (by decide)
    · exact secondBasisInputAvoids refs phase left .g21 (by
        cases left <;> decide)
    · exact secondBasisInputAvoids refs phase right .g21 (by
        cases right <;> decide)
    · exact secondWriteInputAvoids refs phase refs.refreshG21Product
        .refreshG21Product .g21 rfl (by decide)
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · exact coordinateSeparation .secondFirst .firstFirst
  · exact coordinateSeparation .secondSecond .firstSecond
  · exact coordinateSeparation .secondThird .firstThird

/-- The physical state and scratch packages separate the refreshed `g32`
dot-product phase. -/
lemma secondRefreshG32Separation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs
      state scratch
    LatticeDotRefresh.Separation refs.basis.third refs.basis.second
      (LatticeSecondPairMachine.refreshG32Refs refs) := by
  let refs := LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs
    state scratch
  change LatticeDotRefresh.Separation refs.basis.third refs.basis.second
    (LatticeSecondPairMachine.refreshG32Refs refs)
  have phase : LatticeSecondPairMachine.PhaseSeparation refs :=
    secondPhaseSeparation certificates
  have coordinateSeparation
      (left right : LatticeMetricMachine.BasisCell) :
      LatticeDot.CoordinateAccumulateSeparation
        (LatticeMetricMachine.basisCellInput refs.basis left)
        (LatticeMetricMachine.basisCellInput refs.basis right)
        refs.metric.g32 refs.refreshG32Product := by
    refine {
      leftAvoidsProduct := ?_
      rightAvoidsProduct := ?_
      accumulatorAvoidsProduct := ?_
      leftAvoidsAccumulator := ?_
      rightAvoidsAccumulator := ?_
      productAvoidsAccumulator := ?_ }
    · exact secondBasisInputAvoids refs phase left .refreshG32Product (by
        cases left <;> decide)
    · exact secondBasisInputAvoids refs phase right .refreshG32Product (by
        cases right <;> decide)
    · exact secondWriteInputAvoids refs phase refs.metric.g32 .g32
        .refreshG32Product rfl (by decide)
    · exact secondBasisInputAvoids refs phase left .g32 (by
        cases left <;> decide)
    · exact secondBasisInputAvoids refs phase right .g32 (by
        cases right <;> decide)
    · exact secondWriteInputAvoids refs phase refs.refreshG32Product
        .refreshG32Product .g32 rfl (by decide)
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · exact coordinateSeparation .thirdFirst .secondFirst
  · exact coordinateSeparation .thirdSecond .secondSecond
  · exact coordinateSeparation .thirdThird .secondThird

private def secondReductionInputCell : LatticeSecondReductionInputs.InputCell →
    LatticeSecondPairMachine.TransitionCell
  | .g11 => .g11
  | .g21 => .g21
  | .g31 => .g31
  | .g22 => .g22
  | .g32 => .g32

private def secondReductionMutableCell :
    LatticeSecondReductionInputs.MutableCell →
      LatticeSecondPairMachine.TransitionCell
  | .nu32 => .nu32
  | .d32 => .d32
  | .product => .reductionInputsProduct

private lemma secondReductionMutableCell_injective :
    Function.Injective secondReductionMutableCell := by
  intro left right equal
  cases left <;> cases right <;>
    simp [secondReductionMutableCell] at equal ⊢

/-- The five live Gram reads and three second-reduction words satisfy their
local source/write separation contract. -/
lemma secondReductionInputsSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs
      state scratch
    LatticeSecondReductionInputs.Separation
      (LatticeSecondPairMachine.reductionInputs refs) refs.reductionInputs := by
  let refs := LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs
    state scratch
  change LatticeSecondReductionInputs.Separation
    (LatticeSecondPairMachine.reductionInputs refs) refs.reductionInputs
  have phase : LatticeSecondPairMachine.PhaseSeparation refs :=
    secondPhaseSeparation certificates
  refine {
    inputAvoidsMutable := ?_
    mutableInjective := ?_ }
  · intro source target
    have keyNe := phase.cellKey_ne (secondReductionInputCell source)
      (secondReductionMutableCell target) (by
        cases source <;> cases target <;> decide)
    cases source <;> cases target <;>
      simpa only [LatticeSecondPairMachine.reductionInputs,
        LatticeSecondReductionInputs.inputRef,
        LatticeSecondReductionInputs.mutableKey,
        LatticeSecondReductionInputs.mutableRef,
        SignedWord.writeInput,
          CInputRef.storageKeys, List.mem_singleton, ne_comm, secondReductionInputCell,
        secondReductionMutableCell, LatticeSecondPairMachine.cellKey] using keyNe
  · intro left right equal
    apply secondReductionMutableCell_injective
    apply phase.keyInjective
    cases left <;> cases right <;> exact equal

/-- Second-prefix global key separation supplies the `b3 - mu32*b2`
point-reduction subcontract. -/
lemma secondPrefixReductionSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs
      state scratch
    LatticeArithmetic.PointReduceSeparation
      (SignedWord.writeInput
        refs.division32.output)
      refs.basis.second refs.basis.third refs.reduceProduct := by
  let refs := LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs
    state scratch
  change LatticeArithmetic.PointReduceSeparation
    (SignedWord.writeInput
      refs.division32.output)
    refs.basis.second refs.basis.third refs.reduceProduct
  have phase : LatticeSecondPairMachine.PhaseSeparation refs :=
    secondPhaseSeparation certificates
  have coordinateSeparation (source target : LatticeMetricMachine.BasisCell)
      (different : LatticeSecondPairMachine.basisTransitionCell source ≠
        LatticeSecondPairMachine.basisTransitionCell target) :
      LatticeArithmetic.CoordinateReduceSeparation
        (SignedWord.writeInput
          refs.division32.output)
        (LatticeMetricMachine.basisCellInput refs.basis source)
        (secondBasisWriteRef refs.basis target) refs.reduceProduct := by
    refine {
      coefficientAvoidsProduct := ?_
      sourceAvoidsProduct := ?_
      targetAvoidsProduct := ?_
      coefficientAvoidsTarget := ?_
      sourceAvoidsTarget := ?_
      productAvoidsTarget := ?_ }
    · exact secondWriteInputAvoids refs phase refs.division32.output
        (.division32 .output) .reduceProduct rfl (by decide)
    · exact secondBasisInputAvoids refs phase source .reduceProduct (by
        cases source <;> decide)
    · exact secondWriteInputAvoids refs phase
        (secondBasisWriteRef refs.basis target)
        (LatticeSecondPairMachine.basisTransitionCell target) .reduceProduct
        (secondBasisWriteKey refs target) (by cases target <;> decide)
    · simpa only [secondBasisWriteKey] using
        secondWriteInputAvoids refs phase refs.division32.output
          (.division32 .output)
          (LatticeSecondPairMachine.basisTransitionCell target) rfl (by
            cases target <;> decide)
    · simpa only [secondBasisWriteKey] using
        secondBasisInputAvoids refs phase source
          (LatticeSecondPairMachine.basisTransitionCell target) different
    · simpa only [secondBasisWriteKey] using
        secondWriteInputAvoids refs phase refs.reduceProduct .reduceProduct
          (LatticeSecondPairMachine.basisTransitionCell target) rfl (by
            cases target <;> decide)
  refine {
    first := coordinateSeparation .secondFirst .thirdFirst (by decide)
    second := coordinateSeparation .secondSecond .thirdSecond (by decide)
    third := coordinateSeparation .secondThird .thirdThird (by decide)
    sourceSecondAvoidsFirstTarget := ?_
    sourceThirdAvoidsFirstTarget := ?_
    sourceThirdAvoidsSecondTarget := ?_
    targetFirstAvoidsSecond := ?_
    targetFirstAvoidsThird := ?_
    targetSecondAvoidsFirst := ?_
    targetSecondAvoidsThird := ?_
    targetThirdAvoidsFirst := ?_
    targetThirdAvoidsSecond := ?_ }
  · exact secondBasisInputAvoids refs phase .secondSecond .b31 (by decide)
  · exact secondBasisInputAvoids refs phase .secondThird .b31 (by decide)
  · exact secondBasisInputAvoids refs phase .secondThird .b32 (by decide)
  · exact secondWriteInputAvoids refs phase refs.basis.third.first .b31 .b32
      rfl (by decide)
  · exact secondWriteInputAvoids refs phase refs.basis.third.first .b31 .b33
      rfl (by decide)
  · exact secondWriteInputAvoids refs phase refs.basis.third.second .b32 .b31
      rfl (by decide)
  · exact secondWriteInputAvoids refs phase refs.basis.third.second .b32 .b33
      rfl (by decide)
  · exact secondWriteInputAvoids refs phase refs.basis.third.third .b33 .b31
      rfl (by decide)
  · exact secondWriteInputAvoids refs phase refs.basis.third.third .b33 .b32
      rfl (by decide)

/-- The physical state and reusable scratch packages satisfy the complete
second-prefix separation contract. -/
lemma secondPrefixSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    LatticeSecondPairMachine.Separation
      (LatticeFixedFuelScratchWorkspaceViews.secondMachineRefs
        state scratch) := by
  refine {
    phase := secondPhaseSeparation certificates
    refreshG21 := secondRefreshG21Separation certificates
    refreshG32 := secondRefreshG32Separation certificates
    inputs := secondReductionInputsSeparation certificates
    division32 := secondDivision32Separation certificates
    division31 := secondDivision31Separation certificates
    reduction := secondPrefixReductionSeparation certificates }

/-- The post-reduction view reuses the physical `g31` accumulator and the
first refresh product without aliasing either source point. -/
lemma secondPostRefreshSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeFixedFuelScratchWorkspaceViews.secondPostRefs
      state scratch
    LatticeDotRefresh.Separation refs.machine.basis.third refs.machine.basis.first
      (LatticeSecondPairPostReduction.refreshG31Refs refs) := by
  let refs := LatticeFixedFuelScratchWorkspaceViews.secondPostRefs
    state scratch
  let machine := refs.machine
  change LatticeDotRefresh.Separation machine.basis.third machine.basis.first
    (LatticeSecondPairPostReduction.refreshG31Refs refs)
  have phase : LatticeSecondPairMachine.PhaseSeparation machine :=
    secondPhaseSeparation certificates
  have coordinateSeparation
      (left right : LatticeMetricMachine.BasisCell) :
      LatticeDot.CoordinateAccumulateSeparation
        (LatticeMetricMachine.basisCellInput machine.basis left)
        (LatticeMetricMachine.basisCellInput machine.basis right)
        machine.metric.g31 machine.refreshG21Product := by
    refine {
      leftAvoidsProduct := ?_
      rightAvoidsProduct := ?_
      accumulatorAvoidsProduct := ?_
      leftAvoidsAccumulator := ?_
      rightAvoidsAccumulator := ?_
      productAvoidsAccumulator := ?_ }
    · exact secondBasisInputAvoids machine phase left .refreshG21Product (by
        cases left <;> decide)
    · exact secondBasisInputAvoids machine phase right .refreshG21Product (by
        cases right <;> decide)
    · exact secondWriteInputAvoids machine phase machine.metric.g31 .g31
        .refreshG21Product rfl (by decide)
    · exact secondBasisInputAvoids machine phase left .g31 (by
        cases left <;> decide)
    · exact secondBasisInputAvoids machine phase right .g31 (by
        cases right <;> decide)
    · exact secondWriteInputAvoids machine phase machine.refreshG21Product
        .refreshG21Product .g31 rfl (by decide)
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · exact coordinateSeparation .thirdFirst .firstFirst
  · exact coordinateSeparation .thirdSecond .firstSecond
  · exact coordinateSeparation .thirdThird .firstThird

/-- Post-phase global key separation supplies the `b3 - mu31*b1`
point-reduction subcontract. -/
lemma secondPostReductionSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let post := LatticeFixedFuelScratchWorkspaceViews.secondPostRefs
      state scratch
    LatticeArithmetic.PointReduceSeparation
      (SignedWord.writeInput
        post.machine.division31.output)
      post.machine.basis.first post.machine.basis.third
      post.machine.reduceProduct := by
  let post := LatticeFixedFuelScratchWorkspaceViews.secondPostRefs
    state scratch
  let refs := post.machine
  change LatticeArithmetic.PointReduceSeparation
    (SignedWord.writeInput
      refs.division31.output)
    refs.basis.first refs.basis.third refs.reduceProduct
  have phase : LatticeSecondPairMachine.PhaseSeparation refs :=
    secondPhaseSeparation certificates
  have coordinateSeparation (source target : LatticeMetricMachine.BasisCell)
      (different : LatticeSecondPairMachine.basisTransitionCell source ≠
        LatticeSecondPairMachine.basisTransitionCell target) :
      LatticeArithmetic.CoordinateReduceSeparation
        (SignedWord.writeInput
          refs.division31.output)
        (LatticeMetricMachine.basisCellInput refs.basis source)
        (secondBasisWriteRef refs.basis target) refs.reduceProduct := by
    refine {
      coefficientAvoidsProduct := ?_
      sourceAvoidsProduct := ?_
      targetAvoidsProduct := ?_
      coefficientAvoidsTarget := ?_
      sourceAvoidsTarget := ?_
      productAvoidsTarget := ?_ }
    · exact secondWriteInputAvoids refs phase refs.division31.output
        (.division31 .output) .reduceProduct rfl (by decide)
    · exact secondBasisInputAvoids refs phase source .reduceProduct (by
        cases source <;> decide)
    · exact secondWriteInputAvoids refs phase
        (secondBasisWriteRef refs.basis target)
        (LatticeSecondPairMachine.basisTransitionCell target) .reduceProduct
        (secondBasisWriteKey refs target) (by cases target <;> decide)
    · simpa only [secondBasisWriteKey] using
        secondWriteInputAvoids refs phase refs.division31.output
          (.division31 .output)
          (LatticeSecondPairMachine.basisTransitionCell target) rfl (by
            cases target <;> decide)
    · simpa only [secondBasisWriteKey] using
        secondBasisInputAvoids refs phase source
          (LatticeSecondPairMachine.basisTransitionCell target) different
    · simpa only [secondBasisWriteKey] using
        secondWriteInputAvoids refs phase refs.reduceProduct .reduceProduct
          (LatticeSecondPairMachine.basisTransitionCell target) rfl (by
            cases target <;> decide)
  refine {
    first := coordinateSeparation .firstFirst .thirdFirst (by decide)
    second := coordinateSeparation .firstSecond .thirdSecond (by decide)
    third := coordinateSeparation .firstThird .thirdThird (by decide)
    sourceSecondAvoidsFirstTarget := ?_
    sourceThirdAvoidsFirstTarget := ?_
    sourceThirdAvoidsSecondTarget := ?_
    targetFirstAvoidsSecond := ?_
    targetFirstAvoidsThird := ?_
    targetSecondAvoidsFirst := ?_
    targetSecondAvoidsThird := ?_
    targetThirdAvoidsFirst := ?_
    targetThirdAvoidsSecond := ?_ }
  · exact secondBasisInputAvoids refs phase .firstSecond .b31 (by decide)
  · exact secondBasisInputAvoids refs phase .firstThird .b31 (by decide)
  · exact secondBasisInputAvoids refs phase .firstThird .b32 (by decide)
  · exact secondWriteInputAvoids refs phase refs.basis.third.first .b31 .b32
      rfl (by decide)
  · exact secondWriteInputAvoids refs phase refs.basis.third.first .b31 .b33
      rfl (by decide)
  · exact secondWriteInputAvoids refs phase refs.basis.third.second .b32 .b31
      rfl (by decide)
  · exact secondWriteInputAvoids refs phase refs.basis.third.second .b32 .b33
      rfl (by decide)
  · exact secondWriteInputAvoids refs phase refs.basis.third.third .b33 .b31
      rfl (by decide)
  · exact secondWriteInputAvoids refs phase refs.basis.third.third .b33 .b32
      rfl (by decide)

/-- The reused post-reduction view satisfies its complete local separation
contract. -/
lemma secondPostSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    LatticeSecondPairPostReduction.Separation
      (LatticeFixedFuelScratchWorkspaceViews.secondPostRefs
        state scratch) := by
  refine {
    phase := secondPhaseSeparation certificates
    refresh := secondPostRefreshSeparation certificates
    division := secondDivision31Separation certificates
    reduction := secondPostReductionSeparation certificates }

private lemma secondFullWriteInputAvoids {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} {sourceShape targetShape : CShape}
    (refs : LatticeSecondPairFullMachine.Refs ctx width)
    (keyInjective : Function.Injective
      (LatticeSecondPairFullMachine.cellKey refs))
    (source : CWriteRef ctx sourceShape) (target : CWriteRef ctx targetShape)
    (sourceCell targetCell : LatticeSecondPairFullMachine.Cell)
    (sourceKey : source.toCStorageRef.key =
      LatticeSecondPairFullMachine.cellKey refs sourceCell)
    (targetKey : target.toCStorageRef.key =
      LatticeSecondPairFullMachine.cellKey refs targetCell)
    (different : sourceCell ≠ targetCell) :
    target.toCStorageRef.key ∉ (SignedWord.writeInput source).storageKeys := by
  apply storageRead_avoids_of_key_ne
  rw [sourceKey, targetKey]
  intro equal
  exact different (keyInjective equal)

private lemma secondFullCoordinateInputAvoids {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (refs : LatticeSecondPairFullMachine.Refs ctx width)
    (keyInjective : Function.Injective
      (LatticeSecondPairFullMachine.cellKey refs))
    (source target : CWriteRef ctx (LatticeState.RawSignedWordShape width))
    (sourceCell targetCell : LatticeSecondPairFullMachine.Cell)
    (sourceKey : source.toCStorageRef.key =
      LatticeSecondPairFullMachine.cellKey refs sourceCell)
    (targetKey : target.toCStorageRef.key =
      LatticeSecondPairFullMachine.cellKey refs targetCell)
    (different : sourceCell ≠ targetCell) :
    target.toCStorageRef.key ∉ (LatticeState.coordinateInput source).storageKeys := by
  apply storageRead_avoids_of_key_ne
  rw [sourceKey, targetKey]
  intro equal
  exact different (keyInjective equal)

private def area12SourceCell : LatticeCross.SourceCell →
    LatticeSecondPairFullMachine.Cell
  | .leftFirst => .transition .b11
  | .leftSecond => .transition .b12
  | .leftThird => .transition .b13
  | .rightFirst => .transition .b21
  | .rightSecond => .transition .b22
  | .rightThird => .transition .b23

private def area12MutableCell : LatticeCross.MutableCell →
    LatticeSecondPairFullMachine.Cell
  | .outputFirst => .area12CrossFirst
  | .outputSecond => .area12CrossSecond
  | .outputThird => .area12CrossThird
  | .productLeft => .area12ProductLeft
  | .productRight => .area12ProductRight

private lemma area12MutableCell_injective :
    Function.Injective area12MutableCell := by
  intro left right equal
  cases left <;> cases right <;> simp [area12MutableCell] at equal ⊢

/-- Complete full-machine key separation supplies the first--second squared
area refresh. -/
lemma secondArea12Separation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeFixedFuelScratchWorkspaceViews.secondRefs
      state scratch
    LatticeAreaRefresh.Separation refs.machine.basis.first
      refs.machine.basis.second refs.area12 := by
  let refs := LatticeFixedFuelScratchWorkspaceViews.secondRefs
    state scratch
  change LatticeAreaRefresh.Separation refs.machine.basis.first
    refs.machine.basis.second refs.area12
  have keyInjective : Function.Injective
      (LatticeSecondPairFullMachine.cellKey refs) :=
    secondFullKeyInjective certificates
  refine {
    cross := ?_
    norm := ?_ }
  · refine {
      sourceAvoidsMutable := ?_
      mutableInjective := ?_ }
    · intro source target
      have keyNe :
          LatticeSecondPairFullMachine.cellKey refs (area12SourceCell source) ≠
            LatticeSecondPairFullMachine.cellKey refs (area12MutableCell target) := by
        intro equal
        have mapped := keyInjective equal
        cases source <;> cases target <;> cases mapped
      cases source <;> cases target <;>
        apply storageRead_avoids_of_key_ne <;> exact keyNe
    · intro left right equal
      apply area12MutableCell_injective
      apply keyInjective
      cases left <;> cases right <;> exact equal
  · have coordinateSeparation (source : LatticeCross.MutableCell)
        (sourceRef : CWriteRef ctx (LatticeState.RawSignedWordShape
          (LatticeFixedFuelScratchWorkspaceLayout.Width N)))
        (sourceKey : sourceRef.toCStorageRef.key =
          LatticeSecondPairFullMachine.cellKey refs (area12MutableCell source)) :
        LatticeDot.CoordinateAccumulateSeparation
          (LatticeState.coordinateInput sourceRef)
          (LatticeState.coordinateInput sourceRef) refs.area12.area
          refs.area12.normProduct := by
      refine {
        leftAvoidsProduct := ?_
        rightAvoidsProduct := ?_
        accumulatorAvoidsProduct := ?_
        leftAvoidsAccumulator := ?_
        rightAvoidsAccumulator := ?_
        productAvoidsAccumulator := ?_ }
      · exact secondFullCoordinateInputAvoids refs keyInjective sourceRef
          refs.area12.normProduct (area12MutableCell source) .area12NormProduct
          sourceKey rfl (by cases source <;> decide)
      · exact secondFullCoordinateInputAvoids refs keyInjective sourceRef
          refs.area12.normProduct (area12MutableCell source) .area12NormProduct
          sourceKey rfl (by cases source <;> decide)
      · exact secondFullWriteInputAvoids refs keyInjective refs.area12.area
          refs.area12.normProduct .area12Result .area12NormProduct rfl rfl
          (by decide)
      · exact secondFullCoordinateInputAvoids refs keyInjective sourceRef
          refs.area12.area (area12MutableCell source) .area12Result
          sourceKey rfl (by cases source <;> decide)
      · exact secondFullCoordinateInputAvoids refs keyInjective sourceRef
          refs.area12.area (area12MutableCell source) .area12Result
          sourceKey rfl (by cases source <;> decide)
      · exact secondFullWriteInputAvoids refs keyInjective
          refs.area12.normProduct refs.area12.area .area12NormProduct
          .area12Result rfl rfl (by decide)
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · exact coordinateSeparation .outputFirst refs.area12.cross.first rfl
    · exact coordinateSeparation .outputSecond refs.area12.cross.second rfl
    · exact coordinateSeparation .outputThird refs.area12.cross.third rfl

private def area13SourceCell : LatticeCross.SourceCell →
    LatticeSecondPairFullMachine.Cell
  | .leftFirst => .transition .b11
  | .leftSecond => .transition .b12
  | .leftThird => .transition .b13
  | .rightFirst => .transition .b31
  | .rightSecond => .transition .b32
  | .rightThird => .transition .b33

private def area13MutableCell : LatticeCross.MutableCell →
    LatticeSecondPairFullMachine.Cell
  | .outputFirst => .area13CrossFirst
  | .outputSecond => .area13CrossSecond
  | .outputThird => .area13CrossThird
  | .productLeft => .area13ProductLeft
  | .productRight => .area13ProductRight

private lemma area13MutableCell_injective :
    Function.Injective area13MutableCell := by
  intro left right equal
  cases left <;> cases right <;> simp [area13MutableCell] at equal ⊢

/-- Complete full-machine key separation supplies the first--third squared
area refresh. -/
lemma secondArea13Separation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeFixedFuelScratchWorkspaceViews.secondRefs
      state scratch
    LatticeAreaRefresh.Separation refs.machine.basis.first
      refs.machine.basis.third refs.area13 := by
  let refs := LatticeFixedFuelScratchWorkspaceViews.secondRefs
    state scratch
  change LatticeAreaRefresh.Separation refs.machine.basis.first
    refs.machine.basis.third refs.area13
  have keyInjective : Function.Injective
      (LatticeSecondPairFullMachine.cellKey refs) :=
    secondFullKeyInjective certificates
  refine {
    cross := ?_
    norm := ?_ }
  · refine {
      sourceAvoidsMutable := ?_
      mutableInjective := ?_ }
    · intro source target
      have keyNe :
          LatticeSecondPairFullMachine.cellKey refs (area13SourceCell source) ≠
            LatticeSecondPairFullMachine.cellKey refs (area13MutableCell target) := by
        intro equal
        have mapped := keyInjective equal
        cases source <;> cases target <;> cases mapped
      cases source <;> cases target <;>
        apply storageRead_avoids_of_key_ne <;> exact keyNe
    · intro left right equal
      apply area13MutableCell_injective
      apply keyInjective
      cases left <;> cases right <;> exact equal
  · have coordinateSeparation (source : LatticeCross.MutableCell)
        (sourceRef : CWriteRef ctx (LatticeState.RawSignedWordShape
          (LatticeFixedFuelScratchWorkspaceLayout.Width N)))
        (sourceKey : sourceRef.toCStorageRef.key =
          LatticeSecondPairFullMachine.cellKey refs (area13MutableCell source)) :
        LatticeDot.CoordinateAccumulateSeparation
          (LatticeState.coordinateInput sourceRef)
          (LatticeState.coordinateInput sourceRef) refs.area13.area
          refs.area13.normProduct := by
      refine {
        leftAvoidsProduct := ?_
        rightAvoidsProduct := ?_
        accumulatorAvoidsProduct := ?_
        leftAvoidsAccumulator := ?_
        rightAvoidsAccumulator := ?_
        productAvoidsAccumulator := ?_ }
      · exact secondFullCoordinateInputAvoids refs keyInjective sourceRef
          refs.area13.normProduct (area13MutableCell source) .area13NormProduct
          sourceKey rfl (by cases source <;> decide)
      · exact secondFullCoordinateInputAvoids refs keyInjective sourceRef
          refs.area13.normProduct (area13MutableCell source) .area13NormProduct
          sourceKey rfl (by cases source <;> decide)
      · exact secondFullWriteInputAvoids refs keyInjective refs.area13.area
          refs.area13.normProduct .area13Result .area13NormProduct rfl rfl
          (by decide)
      · exact secondFullCoordinateInputAvoids refs keyInjective sourceRef
          refs.area13.area (area13MutableCell source) .area13Result
          sourceKey rfl (by cases source <;> decide)
      · exact secondFullCoordinateInputAvoids refs keyInjective sourceRef
          refs.area13.area (area13MutableCell source) .area13Result
          sourceKey rfl (by cases source <;> decide)
      · exact secondFullWriteInputAvoids refs keyInjective
          refs.area13.normProduct refs.area13.area .area13NormProduct
          .area13Result rfl rfl (by decide)
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · exact coordinateSeparation .outputFirst refs.area13.cross.first rfl
    · exact coordinateSeparation .outputSecond refs.area13.cross.second rfl
    · exact coordinateSeparation .outputThird refs.area13.cross.third rfl

private def secondBranchFullCell : LatticeSecondLovaszBranch.BranchCell →
    LatticeSecondPairFullMachine.Cell
  | .b11 => .transition .b11
  | .b12 => .transition .b12
  | .b13 => .transition .b13
  | .b21 => .transition .b21
  | .b22 => .transition .b22
  | .b23 => .transition .b23
  | .b31 => .transition .b31
  | .b32 => .transition .b32
  | .b33 => .transition .b33
  | .doubled => .lovaszDoubled
  | .passes => .lovaszPasses
  | .swapScratch => .swapScratch

private lemma secondBranchFullCell_injective :
    Function.Injective secondBranchFullCell := by
  intro left right equal
  cases left <;> cases right <;> simp [secondBranchFullCell] at equal ⊢

/-- Complete full-machine key separation supplies the final second-Lovasz
branch subcontract. -/
lemma secondBranchSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    let refs := LatticeFixedFuelScratchWorkspaceViews.secondRefs
      state scratch
    LatticeSecondLovaszBranch.Separation refs.branch := by
  let refs := LatticeFixedFuelScratchWorkspaceViews.secondRefs
    state scratch
  change LatticeSecondLovaszBranch.Separation refs.branch
  have keyInjective : Function.Injective
      (LatticeSecondPairFullMachine.cellKey refs) :=
    secondFullKeyInjective certificates
  refine {
    keyInjective := ?_
    area12AvoidsDoubled := ?_
    area13AvoidsDoubled := ?_
    area12AvoidsPass := ?_
    area13AvoidsPass := ?_ }
  · intro left right equal
    apply secondBranchFullCell_injective
    apply keyInjective
    cases left <;> cases right <;> exact equal
  · exact secondFullWriteInputAvoids refs keyInjective refs.area12.area
      refs.branch.lovasz.doubled .area12Result .lovaszDoubled rfl rfl
      (by decide)
  · exact secondFullWriteInputAvoids refs keyInjective refs.area13.area
      refs.branch.lovasz.doubled .area13Result .lovaszDoubled rfl rfl
      (by decide)
  · exact secondFullWriteInputAvoids refs keyInjective refs.area12.area
      refs.branch.lovasz.passes .area12Result .lovaszPasses rfl rfl
      (by decide)
  · exact secondFullWriteInputAvoids refs keyInjective refs.area13.area
      refs.branch.lovasz.passes .area13Result .lovaszPasses rfl rfl
      (by decide)

/-- The physical state and reusable scratch packages satisfy the complete
second-pair separation contract. -/
lemma secondSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    LatticeSecondPairFullMachine.Separation
      (LatticeFixedFuelScratchWorkspaceViews.secondRefs
        state scratch) := by
  refine {
    keyInjective := secondFullKeyInjective certificates
    prefixPhase := secondPrefixSeparation certificates
    post := secondPostSeparation certificates
    area12Refresh := secondArea12Separation certificates
    area13Refresh := secondArea13Separation certificates
    branch := secondBranchSeparation certificates }

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelScratchWorkspaceSeparation
