/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Factor.Workspace.Separation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Reusable.Program

/-!
# Physical separation for reusable pair recovery

The reusable pair wrapper clears thirteen entry words before executing the
pair-factor routine.  This module maps those words to the existing state,
wide-target, and nearest-plane packages and closes the reset certificates.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticePairReusableWorkspaceSeparation

open Execution
open Execution.ClassicalWorkspace
open ClassicalRoutines

noncomputable section

private lemma storageRead_not_mem {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} {source : CStorageRef ctx shape} {key : StorageKey}
    (different : source.key ≠ key) : key ∉ (CInputRef.storage source).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton, ne_comm] using different

/-- Physical package and named cell underlying one reset destination. -/
inductive PhysicalCell where
  | state (cell : LatticePairStateWorkspaceLayout.Cell)
  | target (cell : LatticeWideTargetWorkspaceLayout.Cell)
  | nearest (cell : LatticeNearestPlaneScratchWorkspaceLayout.Cell)
deriving DecidableEq

/-- Exact physical identity of one reusable-pair reset word. -/
def physicalCell : LatticePairRecoveryReset.Cell → PhysicalCell
  | .firstFull => .state .firstFull
  | .secondFull => .state .secondFull
  | .basis13 => .state .basis13
  | .basis21 => .state .basis21
  | .basis32 => .state .basis32
  | .basis22 => .state .basis22
  | .basis23 => .state .basis23
  | .basis31 => .state .basis31
  | .basis33 => .state .basis33
  | .targetFirstScratch => .target .firstScratch
  | .targetSecondScratch => .target .secondScratch
  | .targetThird => .state .targetThird
  | .denominatorMagnitude => .nearest .g11

private lemma physicalCell_injective : Function.Injective physicalCell := by
  intro left right equal
  cases left <;> cases right <;> simp [physicalCell] at equal ⊢

/-- Storage key represented by one tagged physical reset cell. -/
def physicalKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : LatticePairFactorWorkspaceSeparation.Cells ctx N) :
    PhysicalCell → StorageKey
  | .state cell =>
      (LatticePairStateWorkspaceLayout.cellRef
        cells.pair.core.state cell).toCStorageRef.key
  | .target cell =>
      (LatticeWideTargetWorkspaceLayout.cellRef
        cells.pair.target cell).toCStorageRef.key
  | .nearest cell =>
      (LatticeNearestPlaneScratchWorkspaceLayout.cellRef
        cells.pair.nearest cell).toCStorageRef.key

private lemma physicalKey_injective {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairFactorWorkspaceSeparation.Cells ctx N}
    (certificates :
      LatticePairFactorWorkspaceSeparation.Certificates transport cells) :
    Function.Injective (physicalKey cells) := by
  intro left right equal
  cases left with
  | state left =>
      cases right with
      | state right =>
          congr 1
          exact LatticePairStateWorkspaceLayout.cellRef_key_injective
            cells.pair.core.state certificates.pair.core.stateDistinct equal
      | target right =>
          exact (certificates.pair.coreTarget.state.keysNe
            (LatticePairStateWorkspaceLayout.cellIndex N left)
            (LatticeWideTargetWorkspaceLayout.cellIndex N right) equal).elim
      | nearest right =>
          exact (certificates.pair.coreNearest.state.keysNe
            (LatticePairStateWorkspaceLayout.cellIndex N left)
            (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N right)
              equal).elim
  | target left =>
      cases right with
      | state right =>
          exact (certificates.pair.coreTarget.state.keysNe
            (LatticePairStateWorkspaceLayout.cellIndex N right)
            (LatticeWideTargetWorkspaceLayout.cellIndex N left)
              equal.symm).elim
      | target right =>
          congr 1
          exact LatticeWideTargetWorkspaceLayout.cellRef_key_injective
            cells.pair.target certificates.pair.targetDistinct equal
      | nearest right =>
          exact (certificates.pair.targetNearest.keysNe
            (LatticeWideTargetWorkspaceLayout.cellIndex N left)
            (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N right)
              equal).elim
  | nearest left =>
      cases right with
      | state right =>
          exact (certificates.pair.coreNearest.state.keysNe
            (LatticePairStateWorkspaceLayout.cellIndex N right)
            (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N left)
              equal.symm).elim
      | target right =>
          exact (certificates.pair.targetNearest.keysNe
            (LatticeWideTargetWorkspaceLayout.cellIndex N right)
            (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N left)
              equal.symm).elim
      | nearest right =>
          congr 1
          exact LatticeNearestPlaneScratchWorkspaceLayout.cellRef_key_injective
            cells.pair.nearest certificates.pair.nearestDistinct equal

/-- Reset-key projection agrees with the tagged physical package map. -/
lemma resetCellKey_eq {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : LatticePairFactorWorkspaceSeparation.Cells ctx N)
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N))
    (cell : LatticePairRecoveryReset.Cell) :
    LatticePairRecoveryReset.cellKey
        (LatticePairFactorWorkspaceSeparation.refs transport cells selection
          firstTerminal secondTerminal parameter) cell =
      physicalKey cells (physicalCell cell) := by
  cases cell <;> rfl

/-- Physical distinctness supplies the thirteen-word reset separation. -/
lemma resetSeparation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairFactorWorkspaceSeparation.Cells ctx N}
    (certificates :
      LatticePairFactorWorkspaceSeparation.Certificates transport cells)
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticePairRecoveryReset.Separation
      (LatticePairFactorWorkspaceSeparation.refs transport cells selection
        firstTerminal secondTerminal parameter) := by
  refine ⟨?_⟩
  intro left right equal
  apply physicalCell_injective
  apply physicalKey_injective certificates
  simpa only [resetCellKey_eq transport cells selection firstTerminal secondTerminal
    parameter] using equal

/-- Avoiding the three physical reset packages supplies its caller frame. -/
lemma resetCallerFrame_of_physical {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}
    (transport : Transport outer ctx)
    (cells : LatticePairFactorWorkspaceSeparation.Cells ctx N)
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N))
    (other : CInputRef ctx shape)
    (avoidsState : ∀ cell, ((LatticePairStateWorkspaceLayout.cellRef
        cells.pair.core.state cell).toCStorageRef.key ∉ other.storageKeys))
    (avoidsTarget : ∀ cell, ((LatticeWideTargetWorkspaceLayout.cellRef
        cells.pair.target cell).toCStorageRef.key ∉ other.storageKeys))
    (avoidsNearest : ∀ cell, ((LatticeNearestPlaneScratchWorkspaceLayout.cellRef
        cells.pair.nearest cell).toCStorageRef.key ∉ other.storageKeys)) :
    LatticePairRecoveryReset.CallerFrameAvoids
      (LatticePairFactorWorkspaceSeparation.refs transport cells selection
        firstTerminal secondTerminal parameter) other := by
  intro cell
  rw [resetCellKey_eq]
  cases cell <;> first | exact avoidsState _ | exact avoidsTarget _ |
    exact avoidsNearest _

private lemma resetFrame_outerInput {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}
    (transport : Transport outer ctx)
    (cells : LatticePairFactorWorkspaceSeparation.Cells ctx N)
    (certificates :
      LatticePairFactorWorkspaceSeparation.Certificates transport cells)
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N))
    (other : CInputRef outer shape) :
    LatticePairRecoveryReset.CallerFrameAvoids
      (LatticePairFactorWorkspaceSeparation.refs transport cells selection
        firstTerminal secondTerminal parameter)
      (transport.liftInput other) := by
  apply resetCallerFrame_of_physical transport cells selection firstTerminal
    secondTerminal parameter
  · intro cell
    simpa only [LatticePairStateWorkspaceLayout.cellRef_key] using
      (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids
        cells.pair.core.state transport certificates.pair.core.stateSeparated other
          (LatticePairStateWorkspaceLayout.cellIndex N cell))
  · intro cell
    simpa only [LatticeWideTargetWorkspaceLayout.cellRef_key] using
      (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids cells.pair.target transport
        certificates.pair.targetSeparated other
          (LatticeWideTargetWorkspaceLayout.cellIndex N cell))
  · intro cell
    simpa only [LatticeNearestPlaneScratchWorkspaceLayout.cellRef_key] using
      (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids cells.pair.nearest transport
        certificates.pair.nearestSeparated other
          (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N cell))

private lemma resetFrame_quadraticCell {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : LatticePairFactorWorkspaceSeparation.Cells ctx N)
    (certificates :
      LatticePairFactorWorkspaceSeparation.Certificates transport cells)
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N))
    (source : QuadraticScratchLayout.Cell) :
    LatticePairRecoveryReset.CallerFrameAvoids
      (LatticePairFactorWorkspaceSeparation.refs transport cells selection
        firstTerminal secondTerminal parameter)
      (FirstAccepted.cellRead
        (QuadraticScratchLayout.cellRef cells.quadratic source)) := by
  apply resetCallerFrame_of_physical transport cells selection firstTerminal
    secondTerminal parameter
  · intro cell
    apply storageRead_not_mem
    exact (certificates.coreQuadratic.state.keysNe
      (LatticePairStateWorkspaceLayout.cellIndex N cell)
      (QuadraticScratchLayout.cellIndex N source)).symm
  · intro cell
    apply storageRead_not_mem
    exact (certificates.targetQuadratic.keysNe
      (LatticeWideTargetWorkspaceLayout.cellIndex N cell)
      (QuadraticScratchLayout.cellIndex N source)).symm
  · intro cell
    apply storageRead_not_mem
    exact (certificates.nearestQuadratic.keysNe
      (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N cell)
      (QuadraticScratchLayout.cellIndex N source)).symm

/-- Complete reset-frame contract for one physical reusable pair. -/
lemma resetFrames {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairFactorWorkspaceSeparation.Cells ctx N}
    (certificates :
      LatticePairFactorWorkspaceSeparation.Certificates transport cells)
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticePairReusableRecovery.ResetFrames
      (LatticePairFactorWorkspaceSeparation.refs transport cells selection
        firstTerminal secondTerminal parameter) := by
  let factorRefs := LatticePairFactorWorkspaceSeparation.refs transport cells
    selection firstTerminal secondTerminal parameter
  have firstTerminalEq : LatticePairReusableRecovery.firstTerminal factorRefs =
      transport.liftInput firstTerminal := by
    rfl
  have secondTerminalEq : LatticePairReusableRecovery.secondTerminal factorRefs =
      transport.liftInput secondTerminal := by
    rfl
  refine {
    firstTerminalBits := ?_
    secondTerminalBits := ?_
    setupParameter := ?_
    setupBase := ?_
    quadraticModulus := ?_
    firstOne := ?_
    firstModulus := ?_
    firstZero := ?_
    secondOne := ?_
    secondModulus := ?_
    secondZero := ?_
    factorAccepted := ?_
    factorSelected := ?_ }
  · intro index cell
    have frame := resetFrame_outerInput transport cells certificates selection
      firstTerminal secondTerminal parameter firstTerminal cell
    rw [firstTerminalEq]
    exact frame
  · intro index cell
    have frame := resetFrame_outerInput transport cells certificates selection
      firstTerminal secondTerminal parameter secondTerminal cell
    rw [secondTerminalEq]
    exact frame
  · exact resetFrame_outerInput transport cells certificates selection
      firstTerminal secondTerminal parameter parameter
  · intro cell
    have frame := resetFrame_outerInput transport cells certificates selection
      firstTerminal secondTerminal parameter parameter cell
    simpa only [factorRefs,
      LatticePairFactorWorkspaceSeparation.refs,
      LatticePairRecoveryWorkspaceViews.factorRefs,
      LatticePairRecoveryWorkspaceViews.candidateRefs,
      LatticeCandidateModularSetup.parameterBaseInput,
      LatticeCandidateSharedWorkspaceLayout.setupRefs, CInputRef.storageKeys,
      ParameterShape, ShorStyle.Canonical.ParameterShape] using frame
  · exact resetFrame_quadraticCell transport cells certificates selection
      firstTerminal secondTerminal parameter .modulus
  · exact resetFrame_quadraticCell transport cells certificates selection
      firstTerminal secondTerminal parameter .one
  · exact resetFrame_quadraticCell transport cells certificates selection
      firstTerminal secondTerminal parameter .modulus
  · exact resetFrame_quadraticCell transport cells certificates selection
      firstTerminal secondTerminal parameter .zero
  · exact resetFrame_quadraticCell transport cells certificates selection
      firstTerminal secondTerminal parameter .one
  · exact resetFrame_quadraticCell transport cells certificates selection
      firstTerminal secondTerminal parameter .modulus
  · exact resetFrame_quadraticCell transport cells certificates selection
      firstTerminal secondTerminal parameter .zero
  · change LatticePairRecoveryReset.CallerFrameAvoids factorRefs
      (QuadraticCheckSeparation.factorInput
        (LatticePairFactorWorkspaceSeparation.liftSelection transport
          selection) .accepted)
    rw [LatticePairFactorWorkspaceSeparation.factorInput_liftSelection]
    exact resetFrame_outerInput transport cells certificates selection
      firstTerminal secondTerminal parameter
        (QuadraticCheckSeparation.factorInput
          selection .accepted)
  · change LatticePairRecoveryReset.CallerFrameAvoids factorRefs
      (QuadraticCheckSeparation.factorInput
        (LatticePairFactorWorkspaceSeparation.liftSelection transport
          selection) .selected)
    rw [LatticePairFactorWorkspaceSeparation.factorInput_liftSelection]
    exact resetFrame_outerInput transport cells certificates selection
      firstTerminal secondTerminal parameter
        (QuadraticCheckSeparation.factorInput
          selection .selected)

/-- Physical avoidance supplies the complete reusable-pair caller frame. -/
lemma callerFrame_of_physical {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}
    (transport : Transport outer ctx)
    (cells : LatticePairFactorWorkspaceSeparation.Cells ctx N)
    (certificates :
      LatticePairFactorWorkspaceSeparation.Certificates transport cells)
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N))
    (other : CInputRef ctx shape)
    (avoidsShared : ∀ cell,
      (ClassicalWorkspace.cellAt cells.pair.core.shared cell).ref.key ∉ other.storageKeys)
    (avoidsSlot : ∀ cell, ((LatticeCandidateSlotWorkspaceLayout.cellRef
        cells.pair.core.slot cell).toCStorageRef.key ∉ other.storageKeys))
    (avoidsState : ∀ cell, ((LatticePairStateWorkspaceLayout.cellRef
        cells.pair.core.state cell).toCStorageRef.key ∉ other.storageKeys))
    (avoidsTarget : ∀ cell, ((LatticeWideTargetWorkspaceLayout.cellRef
        cells.pair.target cell).toCStorageRef.key ∉ other.storageKeys))
    (avoidsLll : ∀ cell, ((LatticeFixedFuelScratchWorkspaceLayout.cellRef
        cells.pair.lll cell).toCStorageRef.key ∉ other.storageKeys))
    (avoidsNearest : ∀ cell, ((LatticeNearestPlaneScratchWorkspaceLayout.cellRef
        cells.pair.nearest cell).toCStorageRef.key ∉ other.storageKeys))
    (avoidsQuadratic : ∀ cell,
      LatticePairFactorWorkspaceSeparation.IsQuadraticMutable cell →
        ((QuadraticScratchLayout.cellRef
            cells.quadratic cell).toCStorageRef.key ∉ other.storageKeys))
    (avoidsFactor : ∀ cell, ((QuadraticCheckSeparation.factorKey
        (LatticePairFactorWorkspaceSeparation.liftSelection transport
          selection) cell) ∉ other.storageKeys)) :
    LatticePairReusableRecovery.CallerFrameAvoids
      (LatticePairFactorWorkspaceSeparation.refs transport cells selection
        firstTerminal secondTerminal parameter) other := by
  constructor
  · exact resetCallerFrame_of_physical transport cells selection firstTerminal
      secondTerminal parameter other avoidsState avoidsTarget avoidsNearest
  · exact LatticePairFactorWorkspaceSeparation.callerFrame_of_physical
      transport cells certificates selection firstTerminal secondTerminal parameter
        other avoidsShared avoidsSlot avoidsState avoidsTarget avoidsLll
          avoidsNearest avoidsQuadratic avoidsFactor

/-- Physical packages supply the complete reusable-pair separation contract. -/
lemma separation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairFactorWorkspaceSeparation.Cells ctx N}
    (certificates :
      LatticePairFactorWorkspaceSeparation.Certificates transport cells)
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (selectorSeparated : LatticePairFactorWorkspaceSeparation.SelectorSeparation selection)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticePairReusableRecovery.Separation
      (LatticePairFactorWorkspaceSeparation.refs transport cells selection
        firstTerminal secondTerminal parameter) where
  reset := resetSeparation certificates selection firstTerminal secondTerminal parameter
  recovery := LatticePairFactorWorkspaceSeparation.separation certificates selection
    selectorSeparated firstTerminal secondTerminal parameter
  resetFrames := resetFrames certificates selection firstTerminal secondTerminal
    parameter

end

end LatticePairReusableWorkspaceSeparation
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
