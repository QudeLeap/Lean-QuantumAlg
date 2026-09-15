/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Views
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Input.Workspace.Separation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Workspace.Separation

/-!
# Physical separation for saved-target nearest-plane recovery

This layer combines the persistent pair state, wide-target scratch,
fixed-fuel scratch, and nearest-plane scratch certificates into the exact
separation contract of the saved-target pair machine.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticePairNearestPlaneWorkspaceSeparation

open Execution
open Execution.ClassicalWorkspace
open ClassicalRoutines
open ClassicalRoutines.NumberTheory
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

private theorem storageRead_not_mem {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} {source : CStorageRef ctx shape} {key : StorageKey}
    (different : source.key ≠ key) : key ∉ (CInputRef.storage source).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton, ne_comm] using different

/-- Exact saved-target pair view for two terminal inputs transported from the
enclosing recovery scope. -/
def pairRefs {kind : ProblemKind} {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : LatticePairRecoveryWorkspace.Cells ctx N)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :
    LatticePairNearestPlaneSavedTarget.Refs ctx N :=
  LatticePairRecoveryWorkspaceViews.pairRefs cells.core.state cells.target
    cells.lll cells.nearest (transport.liftInput firstTerminal)
      (transport.liftInput secondTerminal)

private theorem stateCoordinateAvoidsState {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (distinct : state.Distinct)
    (source target : CWriteRef ctx
      (LatticeState.RawSignedWordShape
        (LatticePairStateWorkspaceLayout.Width N)))
    (sourceCell targetCell : LatticePairStateWorkspaceLayout.Cell)
    (sourceKey : source.toCStorageRef.key =
      (LatticePairStateWorkspaceLayout.cellRef state sourceCell).toCStorageRef.key)
    (targetKey : target.toCStorageRef.key =
      (LatticePairStateWorkspaceLayout.cellRef state targetCell).toCStorageRef.key)
    (different : sourceCell ≠ targetCell) :
    target.toCStorageRef.key ∉ (LatticeState.coordinateInput source).storageKeys := by
  apply storageRead_not_mem
  rw [sourceKey, targetKey]
  intro equal
  exact different
    (LatticePairStateWorkspaceLayout.cellRef_key_injective state distinct equal)

/-- Persistent target and saved-target cells satisfy the literal point-copy
contract. -/
theorem pointCopySeparation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells) :
    LatticeRows.PointCopySeparation
      (LatticePairStateWorkspaceViews.targetRefs cells.core.state)
      (LatticePairStateWorkspaceViews.savedTargetRefs cells.core.state) := by
  let source := LatticePairStateWorkspaceViews.targetRefs cells.core.state
  let saved := LatticePairStateWorkspaceViews.savedTargetRefs cells.core.state
  change LatticeRows.PointCopySeparation source saved
  refine {
    sourceSecondAvoidsFirst := ?_
    sourceThirdAvoidsFirst := ?_
    sourceThirdAvoidsSecond := ?_
    targetFirstAvoidsSecond := ?_
    targetFirstAvoidsThird := ?_
    targetSecondAvoidsThird := ?_ }
  · exact stateCoordinateAvoidsState cells.core.state
      certificates.core.stateDistinct source.second saved.first
        .targetSecond .savedTargetFirst rfl rfl (by decide)
  · exact stateCoordinateAvoidsState cells.core.state
      certificates.core.stateDistinct source.third saved.first
        .targetThird .savedTargetFirst rfl rfl (by decide)
  · exact stateCoordinateAvoidsState cells.core.state
      certificates.core.stateDistinct source.third saved.second
        .targetThird .savedTargetSecond rfl rfl (by decide)
  · exact stateCoordinateAvoidsState cells.core.state
      certificates.core.stateDistinct saved.first saved.second
        .savedTargetFirst .savedTargetSecond rfl rfl (by decide)
  · exact stateCoordinateAvoidsState cells.core.state
      certificates.core.stateDistinct saved.first saved.third
        .savedTargetFirst .savedTargetThird rfl rfl (by decide)
  · exact stateCoordinateAvoidsState cells.core.state
      certificates.core.stateDistinct saved.second saved.third
        .savedTargetSecond .savedTargetThird rfl rfl (by decide)

private theorem statePointCopyFrame {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (source : CWriteRef ctx
      (LatticeState.RawSignedWordShape
        (LatticePairStateWorkspaceLayout.Width N)))
    (sourceCell : LatticePairStateWorkspaceLayout.Cell)
    (sourceKey : source.toCStorageRef.key =
      (LatticePairStateWorkspaceLayout.cellRef
        cells.core.state sourceCell).toCStorageRef.key)
    (firstNe : sourceCell ≠ .savedTargetFirst)
    (secondNe : sourceCell ≠ .savedTargetSecond)
    (thirdNe : sourceCell ≠ .savedTargetThird) :
    LatticePairNearestPlaneSavedTarget.PointCopyFrameAvoids
      (LatticePairStateWorkspaceViews.savedTargetRefs cells.core.state)
      (LatticeState.coordinateInput source) := by
  let saved := LatticePairStateWorkspaceViews.savedTargetRefs cells.core.state
  change LatticePairNearestPlaneSavedTarget.PointCopyFrameAvoids saved
    (LatticeState.coordinateInput source)
  refine ⟨?_, ?_, ?_⟩
  · exact stateCoordinateAvoidsState cells.core.state
      certificates.core.stateDistinct source saved.first sourceCell
        .savedTargetFirst sourceKey rfl firstNe
  · exact stateCoordinateAvoidsState cells.core.state
      certificates.core.stateDistinct source saved.second sourceCell
        .savedTargetSecond sourceKey rfl secondNe
  · exact stateCoordinateAvoidsState cells.core.state
      certificates.core.stateDistinct source saved.third sourceCell
        .savedTargetThird sourceKey rfl thirdNe

/-- Copying the original target preserves every input consumed by the
nearest-plane phase. -/
theorem nearestInputCopyFrames {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :
    LatticePairNearestPlaneSavedTarget.NearestInputCopyFrames
      (pairRefs transport cells firstTerminal secondTerminal) := by
  let refs := pairRefs transport cells firstTerminal secondTerminal
  let state := cells.core.state
  change LatticePairNearestPlaneSavedTarget.NearestInputCopyFrames refs
  refine {
    basisFirst := ?_
    basisSecond := ?_
    basisThird := ?_
    basisFourth := ?_
    basisFifth := ?_
    basisSixth := ?_
    basisSeventh := ?_
    basisEighth := ?_
    basisNinth := ?_
    targetFirst := ?_
    targetSecond := ?_
    targetThird := ?_ }
  · change LatticePairNearestPlaneSavedTarget.PointCopyFrameAvoids
      (LatticePairStateWorkspaceViews.savedTargetRefs state)
      (LatticeState.coordinateInput
        (LatticePairStateWorkspaceLayout.cellRef state .basis11))
    exact statePointCopyFrame certificates _ .basis11 rfl
      (by decide) (by decide) (by decide)
  · change LatticePairNearestPlaneSavedTarget.PointCopyFrameAvoids
      (LatticePairStateWorkspaceViews.savedTargetRefs state)
      (LatticeState.coordinateInput
        (LatticePairStateWorkspaceLayout.cellRef state .basis12))
    exact statePointCopyFrame certificates _ .basis12 rfl
      (by decide) (by decide) (by decide)
  · change LatticePairNearestPlaneSavedTarget.PointCopyFrameAvoids
      (LatticePairStateWorkspaceViews.savedTargetRefs state)
      (LatticeState.coordinateInput
        (LatticePairStateWorkspaceLayout.cellRef state .basis13))
    exact statePointCopyFrame certificates _ .basis13 rfl
      (by decide) (by decide) (by decide)
  · change LatticePairNearestPlaneSavedTarget.PointCopyFrameAvoids
      (LatticePairStateWorkspaceViews.savedTargetRefs state)
      (LatticeState.coordinateInput
        (LatticePairStateWorkspaceLayout.cellRef state .basis21))
    exact statePointCopyFrame certificates _ .basis21 rfl
      (by decide) (by decide) (by decide)
  · change LatticePairNearestPlaneSavedTarget.PointCopyFrameAvoids
      (LatticePairStateWorkspaceViews.savedTargetRefs state)
      (LatticeState.coordinateInput
        (LatticePairStateWorkspaceLayout.cellRef state .basis22))
    exact statePointCopyFrame certificates _ .basis22 rfl
      (by decide) (by decide) (by decide)
  · change LatticePairNearestPlaneSavedTarget.PointCopyFrameAvoids
      (LatticePairStateWorkspaceViews.savedTargetRefs state)
      (LatticeState.coordinateInput
        (LatticePairStateWorkspaceLayout.cellRef state .basis23))
    exact statePointCopyFrame certificates _ .basis23 rfl
      (by decide) (by decide) (by decide)
  · change LatticePairNearestPlaneSavedTarget.PointCopyFrameAvoids
      (LatticePairStateWorkspaceViews.savedTargetRefs state)
      (LatticeState.coordinateInput
        (LatticePairStateWorkspaceLayout.cellRef state .basis31))
    exact statePointCopyFrame certificates _ .basis31 rfl
      (by decide) (by decide) (by decide)
  · change LatticePairNearestPlaneSavedTarget.PointCopyFrameAvoids
      (LatticePairStateWorkspaceViews.savedTargetRefs state)
      (LatticeState.coordinateInput
        (LatticePairStateWorkspaceLayout.cellRef state .basis32))
    exact statePointCopyFrame certificates _ .basis32 rfl
      (by decide) (by decide) (by decide)
  · change LatticePairNearestPlaneSavedTarget.PointCopyFrameAvoids
      (LatticePairStateWorkspaceViews.savedTargetRefs state)
      (LatticeState.coordinateInput
        (LatticePairStateWorkspaceLayout.cellRef state .basis33))
    exact statePointCopyFrame certificates _ .basis33 rfl
      (by decide) (by decide) (by decide)
  · change LatticePairNearestPlaneSavedTarget.PointCopyFrameAvoids
      (LatticePairStateWorkspaceViews.savedTargetRefs state)
      (LatticeState.coordinateInput
        (LatticePairStateWorkspaceLayout.cellRef state .targetFirst))
    exact statePointCopyFrame certificates _ .targetFirst rfl
      (by decide) (by decide) (by decide)
  · change LatticePairNearestPlaneSavedTarget.PointCopyFrameAvoids
      (LatticePairStateWorkspaceViews.savedTargetRefs state)
      (LatticeState.coordinateInput
        (LatticePairStateWorkspaceLayout.cellRef state .targetSecond))
    exact statePointCopyFrame certificates _ .targetSecond rfl
      (by decide) (by decide) (by decide)
  · change LatticePairNearestPlaneSavedTarget.PointCopyFrameAvoids
      (LatticePairStateWorkspaceViews.savedTargetRefs state)
      (LatticeState.coordinateInput
        (LatticePairStateWorkspaceLayout.cellRef state .targetThird))
    exact statePointCopyFrame certificates _ .targetThird rfl
      (by decide) (by decide) (by decide)
private theorem nearestFrameStateCoordinate {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (source : CWriteRef ctx
      (LatticeState.RawSignedWordShape
        (LatticePairStateWorkspaceLayout.Width N)))
    (sourceCell : LatticePairStateWorkspaceLayout.Cell)
    (sourceKey : source.toCStorageRef.key =
      (LatticePairStateWorkspaceLayout.cellRef
        cells.core.state sourceCell).toCStorageRef.key)
    (avoidsFirst : sourceCell ≠ .targetFirst)
    (avoidsSecond : sourceCell ≠ .targetSecond)
    (avoidsThird : sourceCell ≠ .targetThird) :
    LatticeNearestPlaneThree.FrameAvoids
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        cells.core.state cells.nearest)
      (LatticeState.coordinateInput source) := by
  apply LatticeNearestPlaneScratchWorkspaceSeparation.frameAvoidsStateCoordinate
    ⟨certificates.core.stateDistinct, certificates.nearestDistinct,
      certificates.coreNearest.state⟩ source sourceCell
  · simpa only [LatticeNearestPlaneScratchWorkspaceSeparation.physicalKey]
      using sourceKey
  · exact avoidsFirst
  · exact avoidsSecond
  · exact avoidsThird

/-- The nearest-plane stage preserves the saved target. -/
theorem savedTargetNearestFrames {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :
    LatticePairNearestPlaneSavedTarget.SavedTargetNearestFrames
      (pairRefs transport cells firstTerminal secondTerminal) := by
  let state := cells.core.state
  change LatticePairNearestPlaneSavedTarget.SavedTargetNearestFrames
    (pairRefs transport cells firstTerminal secondTerminal)
  refine ⟨?_, ?_, ?_⟩
  · change LatticeNearestPlaneThree.FrameAvoids
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs state cells.nearest)
      (LatticeState.coordinateInput
        (LatticePairStateWorkspaceLayout.cellRef state .savedTargetFirst))
    exact nearestFrameStateCoordinate certificates _ .savedTargetFirst rfl
      (by decide) (by decide) (by decide)
  · change LatticeNearestPlaneThree.FrameAvoids
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs state cells.nearest)
      (LatticeState.coordinateInput
        (LatticePairStateWorkspaceLayout.cellRef state .savedTargetSecond))
    exact nearestFrameStateCoordinate certificates _ .savedTargetSecond rfl
      (by decide) (by decide) (by decide)
  · change LatticeNearestPlaneThree.FrameAvoids
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs state cells.nearest)
      (LatticeState.coordinateInput
        (LatticePairStateWorkspaceLayout.cellRef state .savedTargetThird))
    exact nearestFrameStateCoordinate certificates _ .savedTargetThird rfl
      (by decide) (by decide) (by decide)

/-- The nearest-plane stage preserves all nine reduced-basis coordinates. -/
theorem basisNearestFrames {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :
    LatticePairNearestPlaneSavedTarget.BasisNearestFrames
      (pairRefs transport cells firstTerminal secondTerminal) := by
  let state := cells.core.state
  change LatticePairNearestPlaneSavedTarget.BasisNearestFrames
    (pairRefs transport cells firstTerminal secondTerminal)
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  all_goals
    change LatticeNearestPlaneThree.FrameAvoids
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs state cells.nearest)
      _
  · exact nearestFrameStateCoordinate certificates _ .basis11 rfl
      (by decide) (by decide) (by decide)
  · exact nearestFrameStateCoordinate certificates _ .basis12 rfl
      (by decide) (by decide) (by decide)
  · exact nearestFrameStateCoordinate certificates _ .basis13 rfl
      (by decide) (by decide) (by decide)
  · exact nearestFrameStateCoordinate certificates _ .basis21 rfl
      (by decide) (by decide) (by decide)
  · exact nearestFrameStateCoordinate certificates _ .basis22 rfl
      (by decide) (by decide) (by decide)
  · exact nearestFrameStateCoordinate certificates _ .basis23 rfl
      (by decide) (by decide) (by decide)
  · exact nearestFrameStateCoordinate certificates _ .basis31 rfl
      (by decide) (by decide) (by decide)
  · exact nearestFrameStateCoordinate certificates _ .basis32 rfl
      (by decide) (by decide) (by decide)
  · exact nearestFrameStateCoordinate certificates _ .basis33 rfl
      (by decide) (by decide) (by decide)

/-- Avoiding every physical package of the pair machine supplies its complete
caller-frame contract. -/
theorem callerFrame_of_physical {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}
    (transport : Transport outer ctx)
    (cells : LatticePairRecoveryWorkspace.Cells ctx N)
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (other : CInputRef ctx shape)
    (avoidsState : ∀ cell, (LatticePairStateWorkspaceLayout.cellRef
        cells.core.state cell).toCStorageRef.key ∉ other.storageKeys)
    (avoidsTarget : ∀ cell, (LatticeWideTargetWorkspaceLayout.cellRef
        cells.target cell).toCStorageRef.key ∉ other.storageKeys)
    (avoidsLll : ∀ cell, (LatticeFixedFuelScratchWorkspaceLayout.cellRef
        cells.lll cell).toCStorageRef.key ∉ other.storageKeys)
    (avoidsNearest : ∀ cell, (LatticeNearestPlaneScratchWorkspaceLayout.cellRef
        cells.nearest cell).toCStorageRef.key ∉ other.storageKeys) :
    LatticePairNearestPlaneSavedTarget.CallerFrameAvoids
      (pairRefs transport cells firstTerminal secondTerminal) other := by
  refine {
    wide := ?_
    copy := ⟨avoidsState .savedTargetFirst,
      avoidsState .savedTargetSecond, avoidsState .savedTargetThird⟩
    nearest := ?_ }
  · change LatticeWideLllMachine.CallerSeparated
      (LatticeWideLllWorkspaceSeparation.wideRefs transport cells
        firstTerminal secondTerminal) other
    exact LatticeWideLllWorkspaceSeparation.callerSeparated_of_physical
      transport cells firstTerminal secondTerminal other avoidsState
        avoidsTarget avoidsLll
  · change LatticeNearestPlaneThree.FrameAvoids
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        cells.core.state cells.nearest) other
    exact LatticeNearestPlaneScratchWorkspaceSeparation.frameAvoids_of_physical
      ⟨certificates.core.stateDistinct, certificates.nearestDistinct,
        certificates.coreNearest.state⟩ other
        avoidsState avoidsNearest

private theorem wideCallerNearestCell {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (source : CWriteRef ctx shape)
    (sourceCell : LatticeNearestPlaneScratchWorkspaceLayout.Cell)
    (sourceKey : source.toCStorageRef.key =
      (LatticeNearestPlaneScratchWorkspaceLayout.cellRef
        cells.nearest sourceCell).toCStorageRef.key) :
    LatticeWideLllMachine.CallerSeparated
      (LatticeWideLllWorkspaceSeparation.wideRefs transport cells
        firstTerminal secondTerminal)
      (SignedWord.writeInput source) := by
  apply LatticeWideLllWorkspaceSeparation.callerSeparated_of_physical
    transport cells firstTerminal secondTerminal (SignedWord.writeInput source)
  · intro cell
    apply storageRead_not_mem
    rw [sourceKey]
    exact (certificates.coreNearest.state.keysNe
      (LatticePairStateWorkspaceLayout.cellIndex N cell)
      (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N sourceCell)).symm
  · intro cell
    apply storageRead_not_mem
    rw [sourceKey]
    exact (certificates.targetNearest.keysNe
      (LatticeWideTargetWorkspaceLayout.cellIndex N cell)
      (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N sourceCell)).symm
  · intro cell
    apply storageRead_not_mem
    rw [sourceKey]
    exact (certificates.lllNearest.keysNe
      (LatticeFixedFuelScratchWorkspaceLayout.cellIndex N cell)
      (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N sourceCell)).symm

/-- Typed reference for the denominator magnitude value. -/
def denominatorMagnitudeRef {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : LatticePairRecoveryWorkspace.Cells ctx N)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :=
  let refs := pairRefs transport cells firstTerminal secondTerminal
  refs.pairNearest.third.denominatorMagnitude

/-- The wide reduction preserves the nearest-plane denominator-magnitude
scratch cell. -/
theorem denominatorMagnitudePreservedByWide {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :
    LatticeWideLllMachine.CallerSeparated
      (pairRefs transport cells firstTerminal secondTerminal).pairNearest.wide
      (SignedWord.writeInput (denominatorMagnitudeRef transport cells
        firstTerminal secondTerminal)) := by
  change LatticeWideLllMachine.CallerSeparated
    (LatticeWideLllWorkspaceSeparation.wideRefs transport cells
      firstTerminal secondTerminal)
    (SignedWord.writeInput
      (LatticeNearestPlaneScratchWorkspaceLayout.cellRef cells.nearest .g11))
  exact wideCallerNearestCell certificates firstTerminal secondTerminal _ .g11 rfl

/-- Every physical allocation certificate combines into the saved-target pair
machine's complete separation contract. -/
theorem separation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N))) :
    LatticePairNearestPlaneSavedTarget.Separation
      (pairRefs transport cells firstTerminal secondTerminal) := by
  refine {
    wide := ?_
    target := ?_
    copy := ?_
    nearest := ?_
    copyPreservesNearestInputs := nearestInputCopyFrames certificates
      firstTerminal secondTerminal
    savedTargetAvoidsNearestWrites := savedTargetNearestFrames certificates
      firstTerminal secondTerminal
    basisAvoidsNearestWrites := basisNearestFrames certificates
      firstTerminal secondTerminal }
  · change LatticeWideLllMachine.Separation
      (LatticeWideLllWorkspaceSeparation.wideRefs transport cells
        firstTerminal secondTerminal)
    exact LatticeWideLllWorkspaceSeparation.separation certificates
      firstTerminal secondTerminal
  · change LatticeWideLllTargetPreservation.TargetPreservationSeparation
      (LatticeWideLllWorkspaceSeparation.wideRefs transport cells
        firstTerminal secondTerminal)
    exact LatticeWideLllWorkspaceSeparation.targetPreservation certificates
      firstTerminal secondTerminal
  · change LatticeRows.PointCopySeparation
      (LatticePairStateWorkspaceViews.targetRefs cells.core.state)
      (LatticePairStateWorkspaceViews.savedTargetRefs cells.core.state)
    exact pointCopySeparation certificates
  · change LatticeNearestPlaneThree.Separation
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        cells.core.state cells.nearest)
    exact LatticeNearestPlaneScratchWorkspaceSeparation.separation
      ⟨certificates.core.stateDistinct, certificates.nearestDistinct,
        certificates.coreNearest.state⟩

end

end LatticePairNearestPlaneWorkspaceSeparation
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
