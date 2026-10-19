/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Workspace.Separation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.NearestPlane.Workspace.Separation

/-!
# Physical separation for pair candidate recovery

This module combines the reusable pair, shared-candidate, and candidate-slot
workspace certificates into the complete separation contract consumed by one
pair-to-candidate recovery invocation.  It contains no execution semantics.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticePairCandidateWorkspaceSeparation

open Execution
open Execution.ClassicalWorkspace
open ClassicalRoutines
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

private lemma storageRead_not_mem {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} {source : CStorageRef ctx shape} {key : StorageKey}
    (different : source.key ≠ key) : key ∉ (CInputRef.storage source).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton, ne_comm] using different

/-- Complete pair-candidate references over the allocated physical packages. -/
def refs {kind : ProblemKind} {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : LatticePairRecoveryWorkspace.Cells ctx N)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticePairCandidateRecovery.Refs ctx N :=
  LatticePairRecoveryWorkspaceViews.candidateRefs
    cells.core.shared cells.core.slot cells.core.state cells.target cells.lll
      cells.nearest (transport.liftInput firstTerminal)
        (transport.liftInput secondTerminal)
          (LatticeCandidateSharedWorkspaceLayout.setupRefs
            cells.core.shared transport parameter)

private lemma pairSource_avoids_key {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat} {target : StorageKey}
    (transport : Transport outer ctx)
    (cells : LatticePairRecoveryWorkspace.Cells ctx N)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N))
    (source : LatticeCandidateSlotFrames.ExternalSourceCell)
    (pairSource : LatticePairCandidateRecovery.IsPairSource source)
    (stateAvoids : ∀ cell,
      (LatticePairStateWorkspaceLayout.cellRef
        cells.core.state cell).toCStorageRef.key ≠ target)
    (nearestAvoids : ∀ cell,
      (LatticeNearestPlaneScratchWorkspaceLayout.cellRef
        cells.nearest cell).toCStorageRef.key ≠ target) :
    target ∉ (LatticeCandidateSlotFrames.externalSourceInput
      (refs transport cells firstTerminal secondTerminal parameter).scan
        source).storageKeys := by
  cases source with
  | candidateEntry entry =>
      cases entry with
      | basisFirstFirst => exact storageRead_not_mem (stateAvoids .basis11)
      | basisFirstSecond => exact storageRead_not_mem (stateAvoids .basis12)
      | basisFirstThird => exact storageRead_not_mem (stateAvoids .basis13)
      | basisSecondFirst => exact storageRead_not_mem (stateAvoids .basis21)
      | basisSecondSecond => exact storageRead_not_mem (stateAvoids .basis22)
      | basisSecondThird => exact storageRead_not_mem (stateAvoids .basis23)
      | basisThirdFirst => exact storageRead_not_mem (stateAvoids .basis31)
      | basisThirdSecond => exact storageRead_not_mem (stateAvoids .basis32)
      | basisThirdThird => exact storageRead_not_mem (stateAvoids .basis33)
      | centerFirst => exact storageRead_not_mem (nearestAvoids .targetDotSecond)
      | centerSecond => exact storageRead_not_mem (nearestAvoids .secondOutput)
      | centerThird => exact storageRead_not_mem (nearestAvoids .thirdOutput)
  | originalTarget coordinate =>
      cases coordinate with
      | first => exact storageRead_not_mem (stateAvoids .savedTargetFirst)
      | second => exact storageRead_not_mem (stateAvoids .savedTargetSecond)
      | third => exact storageRead_not_mem (stateAvoids .savedTargetThird)
  | zero | upperBound | modulus | generator | targetPower =>
      simp only [LatticePairCandidateRecovery.IsPairSource] at pairSource

private lemma pairSource_avoids_shared {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : LatticePairRecoveryWorkspace.Cells ctx N)
    (certificates :
      LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N))
    (source : LatticeCandidateSlotFrames.ExternalSourceCell)
    (pairSource : LatticePairCandidateRecovery.IsPairSource source)
    (target : Fin
      (LatticeCandidateSharedWorkspaceLayout.shapes N).length) :
    (ClassicalWorkspace.cellAt cells.core.shared target).ref.toCStorageRef.key ∉
      (LatticeCandidateSlotFrames.externalSourceInput
        (refs transport cells firstTerminal secondTerminal parameter).scan
        source).storageKeys := by
  apply pairSource_avoids_key transport cells firstTerminal secondTerminal
    parameter source pairSource
  · intro cell
    exact (certificates.core.sharedState.keysNe target
      (LatticePairStateWorkspaceLayout.cellIndex N cell)).symm
  · intro cell
    exact (certificates.coreNearest.shared.keysNe target
      (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N cell)).symm

private lemma scanExternalAvoids {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : LatticePairRecoveryWorkspace.Cells ctx N)
    (certificates :
      LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticeCandidateSlotWorkspaceSeparation.ExternalAvoids cells.core.slot
      (refs transport cells firstTerminal secondTerminal parameter).scan := by
  intro source target
  cases source with
  | candidateEntry entry =>
      apply pairSource_avoids_key transport cells firstTerminal secondTerminal
        parameter (.candidateEntry entry) trivial
      · intro cell
        exact (certificates.core.slotState.keysNe
          (LatticeCandidateSlotWorkspaceLayout.cellIndex N target)
          (LatticePairStateWorkspaceLayout.cellIndex N cell)).symm
      · intro cell
        exact (certificates.coreNearest.slot.keysNe
          (LatticeCandidateSlotWorkspaceLayout.cellIndex N target)
          (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N cell)).symm
  | originalTarget coordinate =>
      apply pairSource_avoids_key transport cells firstTerminal secondTerminal
        parameter (.originalTarget coordinate) trivial
      · intro cell
        exact (certificates.core.slotState.keysNe
          (LatticeCandidateSlotWorkspaceLayout.cellIndex N target)
          (LatticePairStateWorkspaceLayout.cellIndex N cell)).symm
      · intro cell
        exact (certificates.coreNearest.slot.keysNe
          (LatticeCandidateSlotWorkspaceLayout.cellIndex N target)
          (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N cell)).symm
  | zero =>
      apply storageRead_not_mem
      exact certificates.core.sharedSlot.keysNe
        (LatticeCandidateSharedWorkspaceLayout.zeroIndex N)
        (LatticeCandidateSlotWorkspaceLayout.cellIndex N target)
  | upperBound =>
      apply storageRead_not_mem
      exact certificates.core.sharedSlot.keysNe
        (LatticeCandidateSharedWorkspaceLayout.upperBoundIndex N)
        (LatticeCandidateSlotWorkspaceLayout.cellIndex N target)
  | modulus =>
      apply storageRead_not_mem
      exact certificates.core.sharedSlot.keysNe
        (LatticeCandidateSharedWorkspaceLayout.modulusIndex N)
        (LatticeCandidateSlotWorkspaceLayout.cellIndex N target)
  | generator =>
      apply storageRead_not_mem
      exact certificates.core.sharedSlot.keysNe
        (LatticeCandidateSharedWorkspaceLayout.generatorIndex N)
        (LatticeCandidateSlotWorkspaceLayout.cellIndex N target)
  | targetPower =>
      apply storageRead_not_mem
      exact certificates.core.sharedSlot.keysNe
        (LatticeCandidateSharedWorkspaceLayout.targetPowerIndex N)
        (LatticeCandidateSlotWorkspaceLayout.cellIndex N target)

private lemma scanCallerFrame_of_physical {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}
    (transport : Transport outer ctx)
    (cells : LatticePairRecoveryWorkspace.Cells ctx N)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N))
    (other : CInputRef ctx shape)
    (avoidsSlot : ∀ cell, (LatticeCandidateSlotWorkspaceLayout.cellRef
        cells.core.slot cell).toCStorageRef.key ∉ other.storageKeys) :
    LatticeCandidateSlotFrames.CallerFrameAvoids
      (refs transport cells firstTerminal secondTerminal parameter).scan
        other := by
  let scan := (refs transport cells firstTerminal secondTerminal parameter).scan
  have avoids (cell : LatticeCandidateSlotFrames.MutableCell) :
      (LatticeCandidateSlotFrames.mutableKey scan cell) ∉ other.storageKeys := by
    change (LatticeCandidateSlotFrames.mutableKey
        (LatticeCandidateSlotWorkspaceViews.slotRefs cells.core.slot
          (LatticePairRecoveryWorkspaceViews.pairRefs cells.core.state
            cells.target cells.lll cells.nearest
              (transport.liftInput firstTerminal)
                (transport.liftInput secondTerminal))
          (LatticePairRecoveryWorkspaceViews.nearestOutputRoles
            cells.core.state cells.target cells.lll cells.nearest
              (transport.liftInput firstTerminal)
                (transport.liftInput secondTerminal))
          (LatticeCandidateSharedWorkspaceLayout.constantRefs cells.core.shared)
          (LatticeCandidateSharedWorkspaceLayout.setupRefs
            cells.core.shared transport parameter)) cell) ∉ other.storageKeys
    rw [LatticeCandidateSlotWorkspaceSeparation.mutableKey_eq_cellRef]
    exact avoidsSlot (LatticeCandidateSlotWorkspaceSeparation.physicalCell cell)
  exact {
    distance := fun cell _ => avoids cell
    near := fun cell _ => avoids cell
    exponent := fun cell _ => avoids cell
    power := fun cell _ => avoids cell
    selector := fun cell _ => avoids cell }

private lemma pairPreservesParameter {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : LatticePairRecoveryWorkspace.Cells ctx N)
    (certificates :
      LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticePairNearestPlaneSavedTarget.CallerFrameAvoids
      (refs transport cells firstTerminal secondTerminal parameter).pair
      (transport.liftInput parameter) := by
  apply LatticePairNearestPlaneWorkspaceSeparation.callerFrame_of_physical
    transport cells certificates firstTerminal secondTerminal
      (transport.liftInput parameter)
  · intro cell
    exact ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids cells.core.state transport
      certificates.core.stateSeparated parameter
        (LatticePairStateWorkspaceLayout.cellIndex N cell)
  · intro cell
    exact ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids cells.target transport
      certificates.targetSeparated parameter
        (LatticeWideTargetWorkspaceLayout.cellIndex N cell)
  · intro cell
    exact ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids cells.lll transport
      certificates.lllSeparated parameter
        (LatticeFixedFuelScratchWorkspaceLayout.cellIndex N cell)
  · intro cell
    exact ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids cells.nearest transport
      certificates.nearestSeparated parameter
        (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N cell)

private lemma pairPreservesParameterBase {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : LatticePairRecoveryWorkspace.Cells ctx N)
    (certificates :
      LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticePairNearestPlaneSavedTarget.CallerFrameAvoids
      (refs transport cells firstTerminal secondTerminal parameter).pair
      (LatticeCandidateModularSetup.parameterBaseInput
        (refs transport cells firstTerminal secondTerminal parameter).setup) := by
  apply LatticePairNearestPlaneWorkspaceSeparation.callerFrame_of_physical
    transport cells certificates firstTerminal secondTerminal
      (LatticeCandidateModularSetup.parameterBaseInput
        (refs transport cells firstTerminal secondTerminal parameter).setup)
  · intro cell
    exact ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids
      cells.core.state transport certificates.core.stateSeparated parameter
        (LatticePairStateWorkspaceLayout.cellIndex N cell)
  · intro cell
    exact ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids
      cells.target transport certificates.targetSeparated parameter
        (LatticeWideTargetWorkspaceLayout.cellIndex N cell)
  · intro cell
    exact ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids
      cells.lll transport certificates.lllSeparated parameter
        (LatticeFixedFuelScratchWorkspaceLayout.cellIndex N cell)
  · intro cell
    exact ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids
      cells.nearest transport certificates.nearestSeparated parameter
        (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N cell)

/-- Avoiding every physical package supplies the full candidate caller frame. -/
lemma callerFrame_of_physical {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}
    (transport : Transport outer ctx)
    (cells : LatticePairRecoveryWorkspace.Cells ctx N)
    (certificates :
      LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N))
    (other : CInputRef ctx shape)
    (avoidsShared : ∀ cell,
      (ClassicalWorkspace.cellAt cells.core.shared cell).ref.toCStorageRef.key ∉ other.storageKeys)
    (avoidsSlot : ∀ cell, (LatticeCandidateSlotWorkspaceLayout.cellRef
        cells.core.slot cell).toCStorageRef.key ∉ other.storageKeys)
    (avoidsState : ∀ cell, (LatticePairStateWorkspaceLayout.cellRef
        cells.core.state cell).toCStorageRef.key ∉ other.storageKeys)
    (avoidsTarget : ∀ cell, (LatticeWideTargetWorkspaceLayout.cellRef
        cells.target cell).toCStorageRef.key ∉ other.storageKeys)
    (avoidsLll : ∀ cell, (LatticeFixedFuelScratchWorkspaceLayout.cellRef
        cells.lll cell).toCStorageRef.key ∉ other.storageKeys)
    (avoidsNearest : ∀ cell, (LatticeNearestPlaneScratchWorkspaceLayout.cellRef
        cells.nearest cell).toCStorageRef.key ∉ other.storageKeys) :
    LatticePairCandidateRecovery.CallerFrameAvoids
      (refs transport cells firstTerminal secondTerminal parameter) other := by
  refine {
    pair := LatticePairNearestPlaneWorkspaceSeparation.callerFrame_of_physical
      transport cells certificates firstTerminal secondTerminal other
        avoidsState avoidsTarget avoidsLll avoidsNearest
    constants := ?_
    setup := ?_
    scan := scanCallerFrame_of_physical transport cells firstTerminal
      secondTerminal parameter other avoidsSlot }
  · exact ⟨avoidsShared (LatticeCandidateSharedWorkspaceLayout.zeroIndex N),
      avoidsShared (LatticeCandidateSharedWorkspaceLayout.upperBoundIndex N)⟩
  · intro cell
    change (LatticeCandidateModularSetup.mutableKey
        (LatticeCandidateSharedWorkspaceLayout.setupRefs
          cells.core.shared transport parameter) cell) ∉ other.storageKeys
    rw [LatticeCandidateSharedWorkspaceLayout.setupMutableKey]
    exact avoidsShared
      (LatticeCandidateSharedWorkspaceLayout.setupIndex N cell)

/-- All physical workspace certificates supply candidate recovery separation. -/
lemma separation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates :
      LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticePairCandidateRecovery.Separation
      (refs transport cells firstTerminal secondTerminal parameter) := by
  let recoveryRefs := refs transport cells firstTerminal secondTerminal parameter
  let setup := LatticeCandidateSharedWorkspaceLayout.setupRefs
    cells.core.shared transport parameter
  have scanFrames : LatticeCandidateSlotFrames.FrameSeparation
      recoveryRefs.scan := by
    change LatticeCandidateSlotFrames.FrameSeparation
      (LatticePairRecoveryWorkspaceViews.candidateRefs cells.core.shared
        cells.core.slot cells.core.state cells.target cells.lll cells.nearest
          (transport.liftInput firstTerminal)
            (transport.liftInput secondTerminal) setup).scan
    exact LatticeCandidateSlotWorkspaceSeparation.frameSeparation
      cells.core.slot certificates.core.slotDistinct
        (LatticePairRecoveryWorkspaceViews.pairRefs cells.core.state
          cells.target cells.lll cells.nearest
            (transport.liftInput firstTerminal)
              (transport.liftInput secondTerminal))
        (LatticePairRecoveryWorkspaceViews.nearestOutputRoles
          cells.core.state cells.target cells.lll cells.nearest
            (transport.liftInput firstTerminal)
              (transport.liftInput secondTerminal))
        (LatticeCandidateSharedWorkspaceLayout.constantRefs cells.core.shared)
        setup (scanExternalAvoids transport cells certificates firstTerminal
          secondTerminal parameter)
  refine {
    pair := ?_
    constants := ?_
    setup := ?_
    scan := LatticeCandidateSlotWorkspaceSeparation.slotSeparation
      recoveryRefs.scan scanFrames
    scanFrames := scanFrames
    pairPreservesSetupParameter := pairPreservesParameter transport cells
      certificates firstTerminal secondTerminal parameter
    pairPreservesSetupBase := pairPreservesParameterBase transport cells
      certificates firstTerminal secondTerminal parameter
    constantsPreservesPairSources := ?_
    constantsPreservesSetupParameter := ?_
    constantsPreservesSetupBase := ?_
    setupPreservesPairSources := ?_
    setupPreservesZero := ?_
    setupPreservesUpperBound := ?_ }
  · change LatticePairNearestPlaneSavedTarget.Separation
      (LatticePairNearestPlaneWorkspaceSeparation.pairRefs transport cells
        firstTerminal secondTerminal)
    exact LatticePairNearestPlaneWorkspaceSeparation.separation certificates
      firstTerminal secondTerminal
  · exact LatticeCandidateSharedWorkspaceLayout.constantSeparation
      cells.core.shared certificates.core.sharedDistinct
  · exact LatticeCandidateSharedWorkspaceLayout.setupSeparation
      cells.core.shared certificates.core.sharedDistinct transport
        certificates.core.sharedSeparated parameter
  · intro source pairSource
    constructor
    · exact pairSource_avoids_shared transport cells certificates
        firstTerminal secondTerminal parameter source pairSource
          (LatticeCandidateSharedWorkspaceLayout.zeroIndex N)
    · exact pairSource_avoids_shared transport cells certificates
        firstTerminal secondTerminal parameter source pairSource
          (LatticeCandidateSharedWorkspaceLayout.upperBoundIndex N)
  · constructor
    · exact ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids
        cells.core.shared transport certificates.core.sharedSeparated parameter
          (LatticeCandidateSharedWorkspaceLayout.zeroIndex N)
    · exact ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids
        cells.core.shared transport certificates.core.sharedSeparated parameter
          (LatticeCandidateSharedWorkspaceLayout.upperBoundIndex N)
  · constructor
    · exact ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids
        cells.core.shared transport certificates.core.sharedSeparated parameter
          (LatticeCandidateSharedWorkspaceLayout.zeroIndex N)
    · exact ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids
        cells.core.shared transport certificates.core.sharedSeparated parameter
          (LatticeCandidateSharedWorkspaceLayout.upperBoundIndex N)
  · intro source pairSource cell
    change
      (LatticeCandidateModularSetup.mutableKey setup cell) ∉
        (LatticeCandidateSlotFrames.externalSourceInput recoveryRefs.scan source).storageKeys
    rw [LatticeCandidateSharedWorkspaceLayout.setupMutableKey]
    exact pairSource_avoids_shared transport cells certificates firstTerminal
      secondTerminal parameter source pairSource
        (LatticeCandidateSharedWorkspaceLayout.setupIndex N cell)
  · intro cell
    change
      (LatticeCandidateModularSetup.mutableKey setup cell) ∉ (LatticeLoading.writeInput
        (LatticeCandidateSharedWorkspaceLayout.constantRefs
          cells.core.shared).zero).storageKeys
    rw [LatticeCandidateSharedWorkspaceLayout.setupMutableKey]
    apply storageRead_not_mem
    intro equal
    have different : LatticeCandidateSharedWorkspaceLayout.zeroIndex N ≠
        LatticeCandidateSharedWorkspaceLayout.setupIndex N cell := by
      intro equal
      have values := congrArg Fin.val equal
      cases cell <;> cases values
    exact different
      (ClassicalWorkspace.workspaceCells_cellAt_key_injective
        cells.core.shared certificates.core.sharedDistinct equal)
  · intro cell
    change
      (LatticeCandidateModularSetup.mutableKey setup cell) ∉ (LatticeLoading.writeInput
        (LatticeCandidateSharedWorkspaceLayout.constantRefs
          cells.core.shared).upperBound).storageKeys
    rw [LatticeCandidateSharedWorkspaceLayout.setupMutableKey]
    apply storageRead_not_mem
    intro equal
    have different : LatticeCandidateSharedWorkspaceLayout.upperBoundIndex N ≠
        LatticeCandidateSharedWorkspaceLayout.setupIndex N cell := by
      intro equal
      have values := congrArg Fin.val equal
      cases cell <;> cases values
    exact different
      (ClassicalWorkspace.workspaceCells_cellAt_key_injective
        cells.core.shared certificates.core.sharedDistinct equal)

end

end LatticePairCandidateWorkspaceSeparation
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
