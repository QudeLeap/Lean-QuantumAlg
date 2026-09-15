/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Target.Workspace.Separation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Input.Workspace.Views
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Workspace.Separation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Input.Target.Preservation

/-!
# Physical wide pair-to-LLL separation

The persistent pair state, wide-target scratch, and fixed-fuel scratch packages
supply every local and cross-stage certificate of the literal wide LLL machine.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeWideLllWorkspaceSeparation

open Execution
open Execution.ClassicalWorkspace
open ClassicalRoutines

noncomputable section

private theorem storageRead_not_mem {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} {source : CStorageRef ctx shape} {key : StorageKey}
    (different : source.key ≠ key) : key ∉ (CInputRef.storage source).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton, ne_comm] using different

private theorem storageRead_not_mem_iff {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} {source : CStorageRef ctx shape} {key : StorageKey} :
    key ∉ (CInputRef.storage source).storageKeys ↔ source.key ≠ key := by
  simp only [CInputRef.storageKeys, List.mem_singleton, ne_comm]

/-- Abbreviation for the local state cell interface. -/
abbrev StateCell := LatticePairStateWorkspaceLayout.Cell

/-- Abbreviation for the local target cell interface. -/
abbrev TargetCell := LatticeWideTargetWorkspaceLayout.Cell

/-- Abbreviation for the local state cell ref interface. -/
abbrev stateCellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : LatticePairStateWorkspaceLayout.Cells ctx N) (cell : StateCell) :=
  LatticePairStateWorkspaceLayout.cellRef cells cell

/-- Abbreviation for the local target cell ref interface. -/
abbrev targetCellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : LatticeWideTargetWorkspaceLayout.Cells ctx N) (cell : TargetCell) :=
  LatticeWideTargetWorkspaceLayout.cellRef cells cell

/-- Exact wide LLL view for two terminal inputs transported from the enclosing
pair-recovery scope. -/
def wideRefs {kind : ProblemKind} {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : LatticePairRecoveryWorkspace.Cells ctx N)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :
    LatticeWideLllMachine.Refs ctx N :=
  LatticeWideLllWorkspaceViews.wideRefs cells.core.state cells.target cells.lll
    (LatticePairStateWorkspaceViews.pairRefs cells.core.state
      (transport.liftInput firstTerminal) (transport.liftInput secondTerminal))

/-- Persistent cells written by the decoder--basis prefix. -/
def prefixCells : List LatticePairStateWorkspaceLayout.Cell :=
  [.firstFull, .firstScratch, .firstJ, .firstK,
    .secondFull, .secondScratch, .secondJ, .secondK,
    .basis11, .basis12, .basis13, .basis21, .basis32]

private theorem writtenKeys_eq_prefixCells {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : LatticePairRecoveryWorkspace.Cells ctx N)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :
    LatticeWideInitializationPrefix.writtenKeys
        (LatticeWideLllMachine.prefixRefs
          (wideRefs transport cells firstTerminal secondTerminal)) =
      prefixCells.map fun cell =>
        (stateCellRef cells.core.state cell).toCStorageRef.key := by
  rfl

private theorem targetKeyAvoidsPrefix {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (target : TargetCell) :
    ∀ key ∈ LatticeWideInitializationPrefix.writtenKeys
        (LatticeWideLllMachine.prefixRefs
          (wideRefs transport cells firstTerminal secondTerminal)),
      (targetCellRef cells.target target).toCStorageRef.key ≠ key := by
  intro key member
  rw [writtenKeys_eq_prefixCells] at member
  rcases List.mem_map.mp member with ⟨source, _sourceMember, rfl⟩
  exact (certificates.coreTarget.state.keysNe
    (LatticePairStateWorkspaceLayout.cellIndex N source)
    (LatticeWideTargetWorkspaceLayout.cellIndex N target)).symm

private def firstScratchInput {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : LatticePairRecoveryWorkspace.Cells ctx N)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :
    CInputRef ctx (.unsignedWord (LatticeWideLllMachine.Width N)) :=
  let refs := wideRefs transport cells firstTerminal secondTerminal
  LatticeTarget.writeInput refs.target.target.first.scratch

private def secondScratchInput {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : LatticePairRecoveryWorkspace.Cells ctx N)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :
    CInputRef ctx (.unsignedWord (LatticeWideLllMachine.Width N)) :=
  let refs := wideRefs transport cells firstTerminal secondTerminal
  LatticeTarget.writeInput refs.target.target.second.scratch

private def targetThirdInput {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : LatticePairRecoveryWorkspace.Cells ctx N)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :
    CInputRef ctx (.unsignedWord (LatticeWideLllMachine.Width N)) :=
  let refs := wideRefs transport cells firstTerminal secondTerminal
  LatticeState.coordinateInput refs.target.target.point.third

private theorem firstScratchAvoidsPrefix {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :
    LatticeWideLllMachine.AvoidsPrefixWrites
      (firstScratchInput transport cells firstTerminal secondTerminal)
      (wideRefs transport cells firstTerminal secondTerminal) := by
  intro key member
  apply storageRead_not_mem
  exact targetKeyAvoidsPrefix certificates firstTerminal secondTerminal
    .firstScratch key member

private theorem secondScratchAvoidsPrefix {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :
    LatticeWideLllMachine.AvoidsPrefixWrites
      (secondScratchInput transport cells firstTerminal secondTerminal)
      (wideRefs transport cells firstTerminal secondTerminal) := by
  intro key member
  apply storageRead_not_mem
  exact targetKeyAvoidsPrefix certificates firstTerminal secondTerminal
    .secondScratch key member

private theorem targetThirdAvoidsPrefix {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :
    LatticeWideLllMachine.AvoidsPrefixWrites
      (targetThirdInput transport cells firstTerminal secondTerminal)
      (wideRefs transport cells firstTerminal secondTerminal) := by
  intro key member
  rw [writtenKeys_eq_prefixCells] at member
  rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
  apply storageRead_not_mem
  intro equal
  have same := LatticePairStateWorkspaceLayout.cellRef_key_injective
    cells.core.state certificates.core.stateDistinct equal
  subst source
  have : LatticePairStateWorkspaceLayout.Cell.targetThird ∉ prefixCells := by
    decide
  exact this sourceMember

/-- Physical state cell underlying one metric basis source. -/
def basisStateCell : LatticeMetricMachine.BasisCell →
    LatticePairStateWorkspaceLayout.Cell
  | .firstFirst => .basis11
  | .firstSecond => .basis12
  | .firstThird => .basis13
  | .secondFirst => .basis21
  | .secondSecond => .basis22
  | .secondThird => .basis23
  | .thirdFirst => .basis31
  | .thirdSecond => .basis32
  | .thirdThird => .basis33

private theorem basisInput_avoids_iff {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (source : LatticeMetricMachine.BasisCell) (key : StorageKey) :
    key ∉ (LatticeMetricMachine.basisCellInput
      (LatticePairStateWorkspaceViews.basisRefs state) source).storageKeys ↔
      (stateCellRef state (basisStateCell source)).toCStorageRef.key ≠ key := by
  cases source <;> exact storageRead_not_mem_iff

private theorem basisInputAvoidsTargetScratch {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (source : LatticeMetricMachine.BasisCell)
    (target : LatticeWideTargetWorkspaceLayout.Cell) :
    (targetCellRef cells.target target).toCStorageRef.key ∉ (LatticeMetricMachine.basisCellInput
      (LatticePairStateWorkspaceViews.basisRefs cells.core.state) source).storageKeys := by
  rw [basisInput_avoids_iff]
  exact certificates.coreTarget.state.keysNe
    (LatticePairStateWorkspaceLayout.cellIndex N (basisStateCell source))
    (LatticeWideTargetWorkspaceLayout.cellIndex N target)

private theorem basisInputAvoidsState {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (distinct : state.Distinct) (source : LatticeMetricMachine.BasisCell)
    (target : LatticePairStateWorkspaceLayout.Cell)
    (different : basisStateCell source ≠ target) :
    (stateCellRef state target).toCStorageRef.key ∉ (LatticeMetricMachine.basisCellInput
      (LatticePairStateWorkspaceViews.basisRefs state) source).storageKeys := by
  rw [basisInput_avoids_iff]
  intro equal
  exact different
    (LatticePairStateWorkspaceLayout.cellRef_key_injective state distinct equal)

private def driverBasisInput {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : LatticePairRecoveryWorkspace.Cells ctx N)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (source : LatticeMetricMachine.BasisCell) :
    CInputRef ctx (.unsignedWord (LatticeWideLllMachine.Width N)) :=
  let refs := wideRefs transport cells firstTerminal secondTerminal
  LatticeMetricMachine.basisCellInput
    refs.initialization.driver.machine.basis source

private theorem driverBasisAvoidsTarget {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (source : LatticeMetricMachine.BasisCell) :
    LatticeWideLllMachine.AvoidsTargetWrites
      (driverBasisInput transport cells firstTerminal secondTerminal source)
      (wideRefs transport cells firstTerminal secondTerminal).target := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact basisInputAvoidsTargetScratch certificates source .firstScaled
  · exact basisInputAvoidsTargetScratch certificates source .secondScaled
  · exact basisInputAvoidsTargetScratch certificates source .firstScratch
  · exact basisInputAvoidsTargetScratch certificates source .firstIsZero
  · exact basisInputAvoidsTargetScratch certificates source .firstBelowHalf
  · exact basisInputAvoidsState cells.core.state certificates.core.stateDistinct
      source .targetFirst (by cases source <;> decide)
  · exact basisInputAvoidsTargetScratch certificates source .secondScratch
  · exact basisInputAvoidsTargetScratch certificates source .secondIsZero
  · exact basisInputAvoidsTargetScratch certificates source .secondBelowHalf
  · exact basisInputAvoidsState cells.core.state certificates.core.stateDistinct
      source .targetSecond (by cases source <;> decide)

/-- All physical allocation certificates combine into the exact separation
contract consumed by the wide pair-to-LLL routine. -/
theorem separation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :
    LatticeWideLllMachine.Separation
      (wideRefs transport cells firstTerminal secondTerminal) := by
  let firstAt := transport.liftInput firstTerminal
  let secondAt := transport.liftInput secondTerminal
  refine {
    prefixSeparation := ?_
    target := ?_
    metric := ?_
    reset := ?_
    driver := ?_
    firstScratchAvoidsPrefix := firstScratchAvoidsPrefix certificates
      firstTerminal secondTerminal
    secondScratchAvoidsPrefix := secondScratchAvoidsPrefix certificates
      firstTerminal secondTerminal
    targetThirdAvoidsPrefix := targetThirdAvoidsPrefix certificates
      firstTerminal secondTerminal
    driverBasisAvoidsTarget := driverBasisAvoidsTarget certificates
      firstTerminal secondTerminal }
  · simpa only [wideRefs, LatticeWideLllWorkspaceViews.wideRefs,
      LatticeWideLllMachine.prefixRefs,
      LatticeFixedFuelScratchWorkspaceViews.initializationRefs,
      LatticePairStateWorkspaceSeparation.prefixRefs, firstAt, secondAt] using
      LatticePairStateWorkspaceSeparation.prefixSeparation cells.core.state
        certificates.core.stateDistinct transport certificates.core.stateSeparated
        firstTerminal secondTerminal
  · simpa only [wideRefs, LatticeWideLllWorkspaceViews.wideRefs,
      LatticeFixedFuelScratchWorkspaceViews.initializationRefs] using
      LatticePairWideTargetWorkspaceSeparation.targetSeparation certificates
        firstAt secondAt
  · change LatticeMetricMachine.Separation
      (LatticePairStateWorkspaceViews.basisRefs cells.core.state)
      (LatticeFixedFuelScratchWorkspaceViews.metricRefs cells.lll)
    exact LatticeFixedFuelScratchWorkspaceSeparation.metricSeparation
      ⟨certificates.core.stateDistinct, certificates.lllDistinct, certificates.coreLll.state⟩
  · change (LatticePairStateWorkspaceViews.machineRefs
      cells.core.state).Separated
    exact LatticeFixedFuelScratchWorkspaceSeparation.machineSeparated (scratch := cells.lll)
      ⟨certificates.core.stateDistinct, certificates.lllDistinct, certificates.coreLll.state⟩
  · change LatticeFixedFuelMachine.Separation
      (LatticeFixedFuelScratchWorkspaceViews.driverRefs
        cells.core.state cells.lll)
    exact LatticeFixedFuelScratchWorkspaceSeparation.driverSeparation
      ⟨certificates.core.stateDistinct, certificates.lllDistinct, certificates.coreLll.state⟩

/-- One of the three persistent target coordinates. -/
inductive TargetCoordinate where
  | first | second | third
deriving DecidableEq

/-- Physical state cell of one target coordinate. -/
def targetStateCell : TargetCoordinate → StateCell
  | .first => .targetFirst
  | .second => .targetSecond
  | .third => .targetThird

/-- Structural input of one physical target coordinate. -/
def targetInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N) :
    TargetCoordinate →
      CInputRef ctx (.unsignedWord (LatticePairStateWorkspaceLayout.Width N))
  | .first =>
      LatticeState.coordinateInput
        (LatticePairStateWorkspaceViews.targetRefs state).first
  | .second =>
      LatticeState.coordinateInput
        (LatticePairStateWorkspaceViews.targetRefs state).second
  | .third =>
      LatticeState.coordinateInput
        (LatticePairStateWorkspaceViews.targetRefs state).third

private theorem targetInput_avoids_iff {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (source : TargetCoordinate) (key : StorageKey) :
    key ∉ (targetInput state source).storageKeys ↔
      (stateCellRef state (targetStateCell source)).toCStorageRef.key ≠ key := by
  cases source <;> exact storageRead_not_mem_iff

private theorem targetState_ne_firstCell (source : TargetCoordinate)
    (target : LatticeFirstPairMachine.TransitionCell) :
    (Sum.inl (targetStateCell source) :
      LatticeFixedFuelScratchWorkspaceSeparation.DriverCell) ≠
        LatticeFixedFuelScratchWorkspaceSeparation.firstTransitionCell target := by
  cases source <;> cases target <;> decide

private theorem secondTransitionInverse_apply
    (cell : LatticeSecondPairMachine.TransitionCell) :
    LatticeFixedFuelScratchWorkspaceSeparation.secondTransitionCellInverse
        (LatticeFixedFuelScratchWorkspaceSeparation.secondTransitionCell cell) =
      some cell := by
  cases cell <;> try rfl
  case division32 cell => cases cell <;> rfl
  case division31 cell => cases cell <;> rfl

private theorem secondFullInverse_apply
    (cell : LatticeSecondPairFullMachine.Cell) :
    LatticeFixedFuelScratchWorkspaceSeparation.secondFullCellInverse
        (LatticeFixedFuelScratchWorkspaceSeparation.secondFullCell cell) =
      some cell := by
  cases cell with
  | transition cell =>
      unfold LatticeFixedFuelScratchWorkspaceSeparation.secondFullCell
        LatticeFixedFuelScratchWorkspaceSeparation.secondFullCellInverse
      rw [secondTransitionInverse_apply]
  | area12ProductLeft => rfl
  | area12ProductRight => rfl
  | area12CrossFirst => rfl
  | area12CrossSecond => rfl
  | area12CrossThird => rfl
  | area12Result => rfl
  | area12NormProduct => rfl
  | area13ProductLeft => rfl
  | area13ProductRight => rfl
  | area13CrossFirst => rfl
  | area13CrossSecond => rfl
  | area13CrossThird => rfl
  | area13Result => rfl
  | area13NormProduct => rfl
  | lovaszDoubled => rfl
  | lovaszPasses => rfl
  | swapScratch => rfl

private theorem targetState_ne_secondCell (source : TargetCoordinate)
    (target : LatticeSecondPairFullMachine.Cell) :
    (Sum.inl (targetStateCell source) :
      LatticeFixedFuelScratchWorkspaceSeparation.DriverCell) ≠
        LatticeFixedFuelScratchWorkspaceSeparation.secondFullCell target := by
  intro equal
  have mapped := congrArg
    LatticeFixedFuelScratchWorkspaceSeparation.secondFullCellInverse equal
  rw [secondFullInverse_apply] at mapped
  cases source <;>
    change (none : Option LatticeSecondPairFullMachine.Cell) = some target at mapped <;>
    cases mapped

private theorem targetInputAvoidsDriverKey {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (source : TargetCoordinate)
    (target : LatticeFixedFuelScratchWorkspaceSeparation.DriverCell)
    (different :
      (Sum.inl (targetStateCell source) :
        LatticeFixedFuelScratchWorkspaceSeparation.DriverCell) ≠ target) :
    (LatticeFixedFuelScratchWorkspaceSeparation.driverKey
        cells.core.state cells.lll target) ∉ (targetInput cells.core.state source).storageKeys := by
  rw [targetInput_avoids_iff]
  change
    LatticeFixedFuelScratchWorkspaceSeparation.driverKey
        cells.core.state cells.lll (.inl (targetStateCell source)) ≠
      LatticeFixedFuelScratchWorkspaceSeparation.driverKey
        cells.core.state cells.lll target
  intro equal
  exact different
    (LatticeFixedFuelScratchWorkspaceSeparation.driverKey_injective
      ⟨certificates.core.stateDistinct, certificates.lllDistinct,
        certificates.coreLll.state⟩ equal)

private theorem targetDriverCallerSeparated {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (source : TargetCoordinate) :
    LatticeFixedFuelMachine.CallerSeparated
      (LatticeFixedFuelScratchWorkspaceViews.driverRefs
        cells.core.state cells.lll)
      (targetInput cells.core.state source) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cell
    change (LatticeFirstPairMachine.cellKey
        (LatticeFixedFuelScratchWorkspaceViews.firstRefs
          cells.core.state cells.lll) cell) ∉ (targetInput cells.core.state source).storageKeys
    rw [LatticeFixedFuelScratchWorkspaceSeparation.firstCellKey_eq_driverKey]
    exact targetInputAvoidsDriverKey certificates source _
      (targetState_ne_firstCell source cell)
  · intro cell
    change (LatticeSecondPairFullMachine.cellKey
        (LatticeFixedFuelScratchWorkspaceViews.secondRefs
          cells.core.state cells.lll) cell) ∉ (targetInput cells.core.state source).storageKeys
    rw [LatticeFixedFuelScratchWorkspaceSeparation.secondFullCellKey_eq_driverKey]
    exact targetInputAvoidsDriverKey certificates source _
      (targetState_ne_secondCell source cell)
  · exact targetInputAvoidsDriverKey certificates source (.inl .secondPhase)
      (by cases source <;> decide)
  · exact targetInputAvoidsDriverKey certificates source (.inl .done)
      (by cases source <;> decide)

private theorem targetInputSeparated {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (source : TargetCoordinate) :
    LatticeWideLllTargetPreservation.TargetInputSeparated
      (wideRefs transport cells firstTerminal secondTerminal)
      (targetInput cells.core.state source) := by
  exact targetDriverCallerSeparated certificates source

/-- The physical state and LLL scratch packages preserve all three target
coordinates through Gram refresh, latch reset, and fixed-fuel reduction. -/
theorem targetPreservation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :
    LatticeWideLllTargetPreservation.TargetPreservationSeparation
      (wideRefs transport cells firstTerminal secondTerminal) := by
  refine ⟨?_, ?_, ?_⟩
  · change LatticeWideLllTargetPreservation.TargetInputSeparated
      (wideRefs transport cells firstTerminal secondTerminal)
      (targetInput cells.core.state .first)
    exact targetInputSeparated certificates firstTerminal secondTerminal .first
  · change LatticeWideLllTargetPreservation.TargetInputSeparated
      (wideRefs transport cells firstTerminal secondTerminal)
      (targetInput cells.core.state .second)
    exact targetInputSeparated certificates firstTerminal secondTerminal .second
  · change LatticeWideLllTargetPreservation.TargetInputSeparated
      (wideRefs transport cells firstTerminal secondTerminal)
      (targetInput cells.core.state .third)
    exact targetInputSeparated certificates firstTerminal secondTerminal .third

/-- Avoiding every physical state, target, and LLL scratch cell is sufficient
for the complete wide-LLL caller-frame contract. -/
theorem callerSeparated_of_physical {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}
    (transport : Transport outer ctx)
    (cells : LatticePairRecoveryWorkspace.Cells ctx N)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (other : CInputRef ctx shape)
    (avoidsState : ∀ cell,
      (stateCellRef cells.core.state cell).toCStorageRef.key ∉ other.storageKeys)
    (avoidsTarget : ∀ cell, (targetCellRef cells.target cell).toCStorageRef.key ∉ other.storageKeys)
    (avoidsLll : ∀ cell, (LatticeFixedFuelScratchWorkspaceLayout.cellRef
        cells.lll cell).toCStorageRef.key ∉ other.storageKeys) :
    LatticeWideLllMachine.CallerSeparated
      (wideRefs transport cells firstTerminal secondTerminal) other := by
  let refs := wideRefs transport cells firstTerminal secondTerminal
  have driverAvoids (cell : LatticeFixedFuelScratchWorkspaceSeparation.DriverCell) :
      (LatticeFixedFuelScratchWorkspaceSeparation.driverKey
          cells.core.state cells.lll cell) ∉ other.storageKeys := by
    rcases cell with cell | cell
    · exact avoidsState cell
    · exact avoidsLll cell
  have prefixWrites :
      LatticeWideLllMachine.AvoidsPrefixWrites other refs := by
    intro key member
    rw [writtenKeys_eq_prefixCells] at member
    rcases List.mem_map.mp member with ⟨cell, _cellMember, rfl⟩
    exact avoidsState cell
  have targetWrites :
      LatticeWideLllMachine.AvoidsTargetWrites other refs.target := by
    refine ⟨avoidsTarget .firstScaled, avoidsTarget .secondScaled,
      avoidsTarget .firstScratch, avoidsTarget .firstIsZero,
      avoidsTarget .firstBelowHalf, ?_, avoidsTarget .secondScratch,
      avoidsTarget .secondIsZero, avoidsTarget .secondBelowHalf, ?_⟩
    · change (stateCellRef cells.core.state .targetFirst).toCStorageRef.key ∉ other.storageKeys
      exact avoidsState .targetFirst
    · change (stateCellRef cells.core.state .targetSecond).toCStorageRef.key ∉ other.storageKeys
      exact avoidsState .targetSecond
  refine {
    decodeTarget := ⟨prefixWrites, targetWrites⟩
    fixedFuel := ?_ }
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro cell
      change (LatticeFirstPairMachine.cellKey
          (LatticeFixedFuelScratchWorkspaceViews.firstRefs
            cells.core.state cells.lll) cell) ∉ other.storageKeys
      rw [LatticeFixedFuelScratchWorkspaceSeparation.firstCellKey_eq_driverKey]
      exact driverAvoids _
    · intro cell
      change (LatticeSecondPairFullMachine.cellKey
          (LatticeFixedFuelScratchWorkspaceViews.secondRefs
            cells.core.state cells.lll) cell) ∉ other.storageKeys
      rw [LatticeFixedFuelScratchWorkspaceSeparation.secondFullCellKey_eq_driverKey]
      exact driverAvoids _
    · change (stateCellRef cells.core.state .secondPhase).toCStorageRef.key ∉ other.storageKeys
      exact avoidsState .secondPhase
    · change (stateCellRef cells.core.state .done).toCStorageRef.key ∉ other.storageKeys
      exact avoidsState .done

end

end LatticeWideLllWorkspaceSeparation
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
