/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Factor.Workspace.Views
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Workspace.Separation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Initialization
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Program.Guarded.Separation

/-!
# Physical separation for one complete pair factor recovery

This module lifts the persistent caller-owned factor selector through the pair
workspace allocation and combines the candidate and quadratic physical
certificates.  It contains no execution semantics.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticePairFactorWorkspaceSeparation

open Execution
open Execution.ClassicalWorkspace
open ClassicalRoutines
open ClassicalRoutines.NumberTheory

noncomputable section

/-- The original six pair packages and the separately allocated quadratic package. -/
structure Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  pair : LatticePairRecoveryWorkspace.Cells ctx N
  quadratic : QuadraticScratchLayout.Cells ctx N

/-- Actual separation of the independent quadratic package from the original pair allocation. -/
structure Certificates {kind : ProblemKind} {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx) (cells : Cells ctx N) : Prop where
  pair : LatticePairRecoveryWorkspace.Certificates transport cells.pair
  quadraticDistinct : cells.quadratic.Distinct
  quadraticSeparated : cells.quadratic.TransportSeparated transport
  coreQuadratic : LatticePairCoreWorkspace.CrossSeparated cells.pair.core cells.quadratic
  targetQuadratic : CrossSeparated cells.pair.target cells.quadratic
  lllQuadratic : CrossSeparated cells.pair.lll cells.quadratic
  nearestQuadratic : CrossSeparated cells.pair.nearest cells.quadratic

/-- Only the canonical selector's five persistent/scratch inequalities are required. -/
structure SelectorSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (selection : FirstAccepted.Refs ctx width) : Prop where
  availableAccepted : selection.available.key ≠ selection.accepted.key
  takeAccepted : selection.take.key ≠ selection.accepted.key
  availableSelected : selection.available.key ≠ selection.selected.key
  takeSelected : selection.take.key ≠ selection.selected.key
  acceptedSelected : selection.accepted.key ≠ selection.selected.key

/-- Place an independently allocated quadratic package after the six existing pair packages. -/
def Cells.ofNested {kind : ProblemKind} {middle inner : RuntimeCtx kind} {N : Nat}
    (pair : LatticePairRecoveryWorkspace.Cells middle N) (transport : Transport middle inner)
    (quadratic : QuadraticScratchLayout.Cells inner N) : Cells inner N where
  pair := pair.transport transport
  quadratic := quadratic

/-- Every original pair certificate survives a later structural workspace allocation. -/
private theorem pairCertificates_transport {kind : ProblemKind}
    {outer middle inner : RuntimeCtx kind} {N : Nat}
    (rootTransport : Transport outer middle) (transport : Transport middle inner)
    (cells : LatticePairRecoveryWorkspace.Cells middle N)
    (certificates : LatticePairRecoveryWorkspace.Certificates rootTransport cells) :
    LatticePairRecoveryWorkspace.Certificates (rootTransport.compose transport)
      (cells.transport transport) where
  core := certificates.core.transport transport
  targetDistinct := workspaceCells_transportCells_distinct transport
    cells.target certificates.targetDistinct
  targetSeparated := workspaceCells_transportCells_transportSeparated rootTransport
    transport cells.target certificates.targetSeparated
  lllDistinct := workspaceCells_transportCells_distinct transport
    cells.lll certificates.lllDistinct
  lllSeparated := workspaceCells_transportCells_transportSeparated rootTransport
    transport cells.lll certificates.lllSeparated
  nearestDistinct := workspaceCells_transportCells_distinct transport
    cells.nearest certificates.nearestDistinct
  nearestSeparated := workspaceCells_transportCells_transportSeparated rootTransport
    transport cells.nearest certificates.nearestSeparated
  coreTarget := certificates.coreTarget.transport transport
  coreLll := certificates.coreLll.transport transport
  coreNearest := certificates.coreNearest.transport transport
  targetLll := certificates.targetLll.transport transport
  targetNearest := certificates.targetNearest.transport transport
  lllNearest := certificates.lllNearest.transport transport

/-- Fresh actual allocation derives all quadratic-to-pair and original-caller exclusions. -/
theorem Certificates.ofNested {kind : ProblemKind} {outer middle inner : RuntimeCtx kind}
    {N : Nat} (rootTransport : Transport outer middle) (transport : Transport middle inner)
    (pair : LatticePairRecoveryWorkspace.Cells middle N)
    (pairCertificates : LatticePairRecoveryWorkspace.Certificates rootTransport pair)
    (quadratic : QuadraticScratchLayout.Cells inner N) (distinct : quadratic.Distinct)
    (separated : quadratic.TransportSeparated transport) :
    Certificates (rootTransport.compose transport) (Cells.ofNested pair transport quadratic) where
  pair := pairCertificates_transport rootTransport transport pair pairCertificates
  quadraticDistinct := distinct
  quadraticSeparated := workspaceCells_transportSeparated_compose
    rootTransport transport quadratic separated
  coreQuadratic := LatticePairCoreWorkspace.crossSeparated_of_nested
    transport pair.core quadratic separated
  targetQuadratic := crossSeparated_of_nested transport pair.target quadratic separated
  lllQuadratic := crossSeparated_of_nested transport pair.lll quadratic separated
  nearestQuadratic := crossSeparated_of_nested transport pair.nearest quadratic separated

private theorem storageRead_not_mem {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} {source : CStorageRef ctx shape} {key : StorageKey}
    (different : source.key ≠ key) : key ∉ (CInputRef.storage source).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton, ne_comm] using different

/-- Transport all four cells of a persistent selector into a deeper scope. -/
def liftSelection {kind : ProblemKind} {outer ctx : RuntimeCtx kind}
    {width : Nat} (transport : Transport outer ctx)
    (selection : FirstAccepted.Refs outer width) :
    FirstAccepted.Refs ctx width where
  accepted := transport.liftWrite selection.accepted
  selected := transport.liftWrite selection.selected
  available := transport.liftWrite selection.available
  take := transport.liftWrite selection.take

/-- Reading one transported selector cell commutes with structural transport. -/
theorem factorInput_liftSelection {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {width : Nat}
    (transport : Transport outer ctx)
    (selection : FirstAccepted.Refs outer width)
    (cell : QuadraticCheckSeparation.FactorCell) :
    QuadraticCheckSeparation.factorInput
        (liftSelection transport selection) cell =
      transport.liftInput
        (QuadraticCheckSeparation.factorInput selection cell) := by
  cases cell with
  | accepted =>
      simpa only [QuadraticCheckSeparation.factorInput,
        QuadraticCheckSeparation.factorShape, liftSelection,
        FirstAccepted.cellRead] using
        (transport.liftWrite_input selection.accepted).symm
  | selected =>
      simpa only [QuadraticCheckSeparation.factorInput,
        QuadraticCheckSeparation.factorShape, liftSelection,
        FirstAccepted.cellRead] using
        (transport.liftWrite_input selection.selected).symm
  | available =>
      simpa only [QuadraticCheckSeparation.factorInput,
        QuadraticCheckSeparation.factorShape, liftSelection,
        FirstAccepted.cellRead] using
        (transport.liftWrite_input selection.available).symm
  | take =>
      simpa only [QuadraticCheckSeparation.factorInput,
        QuadraticCheckSeparation.factorShape, liftSelection,
        FirstAccepted.cellRead] using
        (transport.liftWrite_input selection.take).symm

/-- Complete factor-recovery references over one physical pair allocation. -/
def refs {kind : ProblemKind} {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : Cells ctx N)
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticePairFactorRecovery.Refs ctx N :=
  let setup := LatticeCandidateSharedWorkspaceLayout.setupRefs
    cells.pair.core.shared transport parameter
  let factorSelection := liftSelection transport
    selection
  LatticePairRecoveryWorkspaceViews.factorRefs cells.pair.core.shared
    cells.quadratic cells.pair.core.slot cells.pair.core.state cells.pair.target cells.pair.lll
      cells.pair.nearest (transport.liftInput firstTerminal)
        (transport.liftInput secondTerminal) setup factorSelection

/-- Structural transport preserves the keys of the four selector references. -/
theorem factorKey_liftSelection {kind : ProblemKind} {outer ctx : RuntimeCtx kind}
    {width : Nat} (transport : Transport outer ctx) (selection : FirstAccepted.Refs outer width)
    (cell : QuadraticCheckSeparation.FactorCell) :
    QuadraticCheckSeparation.factorKey (liftSelection transport selection) cell =
      QuadraticCheckSeparation.factorKey selection cell := by
  cases cell <;> exact transport.liftWrite_key _

private theorem factorSeparation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat} (transport : Transport outer ctx)
    (cells : Cells ctx N) (certificates : Certificates transport cells)
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (separated : SelectorSeparation selection) :
    QuadraticCheckSeparation.FactorSeparation cells.quadratic
      (liftSelection transport selection) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [liftSelection, Transport.liftWrite_key] using separated.availableAccepted
  · simpa only [liftSelection, Transport.liftWrite_key] using separated.takeAccepted
  · simpa only [liftSelection, Transport.liftWrite_key] using separated.availableSelected
  · simpa only [liftSelection, Transport.liftWrite_key] using separated.takeSelected
  · simpa only [liftSelection, Transport.liftWrite_key] using separated.acceptedSelected
  · intro factor cell
    rw [factorInput_liftSelection, QuadraticScratchLayout.cellRef_key]
    exact ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids cells.quadratic
      transport certificates.quadraticSeparated
        (QuadraticCheckSeparation.factorInput selection factor)
        (QuadraticScratchLayout.cellIndex N cell)

private theorem shortSelectionSeparation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : Cells ctx N}
    (certificates :
      Certificates transport cells) :
    QuadraticGuardSeparation.ShortSelectionSeparation cells.quadratic
      (LatticeCandidateSlotWorkspaceViews.selectionRefs cells.pair.core.slot) := by
  constructor
  · intro cell
    apply storageRead_not_mem
    change
      (LatticeCandidateSlotWorkspaceLayout.cellRef cells.pair.core.slot
        .shortAccepted).toCStorageRef.key ≠
      (QuadraticScratchLayout.cellRef
        cells.quadratic cell).toCStorageRef.key
    exact certificates.coreQuadratic.slot.keysNe
      (LatticeCandidateSlotWorkspaceLayout.cellIndex N .shortAccepted)
      (QuadraticScratchLayout.cellIndex N cell)
  · intro cell
    apply storageRead_not_mem
    change
      (LatticeCandidateSlotWorkspaceLayout.cellRef cells.pair.core.slot
        .shortSelected).toCStorageRef.key ≠
      (QuadraticScratchLayout.cellRef
        cells.quadratic cell).toCStorageRef.key
    exact certificates.coreQuadratic.slot.keysNe
      (LatticeCandidateSlotWorkspaceLayout.cellIndex N .shortSelected)
      (QuadraticScratchLayout.cellIndex N cell)

private theorem candidateFrame_quadraticCell {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : Cells ctx N)
    (certificates :
      Certificates transport cells)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N))
    (source : QuadraticScratchLayout.Cell) :
    LatticePairCandidateRecovery.CallerFrameAvoids
      (LatticePairCandidateWorkspaceSeparation.refs transport cells.pair
        firstTerminal secondTerminal parameter)
      (FirstAccepted.cellRead
        (QuadraticScratchLayout.cellRef cells.quadratic source)) := by
  apply LatticePairCandidateWorkspaceSeparation.callerFrame_of_physical
    transport cells.pair certificates.pair firstTerminal secondTerminal parameter
  · intro cell
    apply storageRead_not_mem
    exact (certificates.coreQuadratic.shared.keysNe cell
      (QuadraticScratchLayout.cellIndex N source)).symm
  · intro cell
    apply storageRead_not_mem
    exact (certificates.coreQuadratic.slot.keysNe
      (LatticeCandidateSlotWorkspaceLayout.cellIndex N cell)
      (QuadraticScratchLayout.cellIndex N source)).symm
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
    exact (certificates.lllQuadratic.keysNe
      (LatticeFixedFuelScratchWorkspaceLayout.cellIndex N cell)
      (QuadraticScratchLayout.cellIndex N source)).symm
  · intro cell
    apply storageRead_not_mem
    exact (certificates.nearestQuadratic.keysNe
      (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N cell)
      (QuadraticScratchLayout.cellIndex N source)).symm

private theorem candidateFrame_factorCell {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : Cells ctx N)
    (certificates :
      Certificates transport cells)
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N))
    (source : QuadraticCheckSeparation.FactorCell) :
    LatticePairCandidateRecovery.CallerFrameAvoids
      (LatticePairCandidateWorkspaceSeparation.refs transport cells.pair
        firstTerminal secondTerminal parameter)
      (QuadraticCheckSeparation.factorInput
        (liftSelection transport
          selection) source) := by
  rw [factorInput_liftSelection]
  let outerInput := QuadraticCheckSeparation.factorInput
    selection source
  apply LatticePairCandidateWorkspaceSeparation.callerFrame_of_physical
    transport cells.pair certificates.pair firstTerminal secondTerminal parameter
  · intro cell
    exact ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids
      cells.pair.core.shared transport certificates.pair.core.sharedSeparated outerInput cell
  · intro cell
    simpa only [LatticeCandidateSlotWorkspaceLayout.cellRef_key] using
      (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids
        cells.pair.core.slot transport certificates.pair.core.slotSeparated outerInput
          (LatticeCandidateSlotWorkspaceLayout.cellIndex N cell))
  · intro cell
    simpa only [LatticePairStateWorkspaceLayout.cellRef_key] using
      (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids
        cells.pair.core.state transport certificates.pair.core.stateSeparated outerInput
          (LatticePairStateWorkspaceLayout.cellIndex N cell))
  · intro cell
    simpa only [LatticeWideTargetWorkspaceLayout.cellRef_key] using
      (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids cells.pair.target transport
        certificates.pair.targetSeparated outerInput
          (LatticeWideTargetWorkspaceLayout.cellIndex N cell))
  · intro cell
    simpa only [LatticeFixedFuelScratchWorkspaceLayout.cellRef_key] using
      (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids cells.pair.lll transport
        certificates.pair.lllSeparated outerInput
          (LatticeFixedFuelScratchWorkspaceLayout.cellIndex N cell))
  · intro cell
    simpa only [LatticeNearestPlaneScratchWorkspaceLayout.cellRef_key] using
      (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids cells.pair.nearest transport
        certificates.pair.nearestSeparated outerInput
          (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N cell))

/-- Quadratic cells written by guarded recovery, excluding its three constants. -/
def IsQuadraticMutable : QuadraticScratchLayout.Cell → Prop
  | .modulus | .one | .zero => False
  | _ => True

private theorem quadraticCandidatesFrame {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} {shape : CShape} (cells : QuadraticScratchLayout.Cells ctx N)
    (shortLog : CInputRef ctx (.unsignedWord (QuadraticScratchLayout.ShortWidth N)))
    (other : CInputRef ctx shape)
    (avoids : ∀ cell, IsQuadraticMutable cell →
      (QuadraticScratchLayout.cellRef cells cell).key ∉ other.storageKeys) :
    QuadraticCandidates.CallerFrameAvoids (QuadraticScratchViews.candidateRefs cells shortLog)
      other := by
  apply QuadraticPrefixSeparation.candidateCallerFrame cells shortLog other
  exact ⟨avoids .center (by trivial), avoids .centerSquare (by trivial),
    avoids .subtractLessThan (by trivial), avoids .subtractOutput (by trivial),
    avoids .sqrtWideInput (by trivial), avoids .sqrtRoot (by trivial),
    avoids .sqrtHalf (by trivial), avoids .sqrtMidCarry (by trivial),
    avoids .sqrtSquare (by trivial), avoids .sqrtTooLarge (by trivial),
    avoids .sqrtTake (by trivial), avoids .sqrtOutput (by trivial),
    avoids .centerWide (by trivial), avoids .rootWide (by trivial),
    avoids .firstLessThan (by trivial), avoids .firstOutput (by trivial),
    avoids .secondCandidate (by trivial)⟩

private theorem quadraticSelectFrame {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} {shape : CShape} (cells : QuadraticScratchLayout.Cells ctx N)
    (candidate : CInputRef ctx (.unsignedWord (QuadraticScratchLayout.CandidateWidth N)))
    (selection : FirstAccepted.Refs ctx (QuadraticScratchLayout.CandidateWidth N))
    (other : CInputRef ctx shape)
    (avoids : ∀ cell, IsQuadraticMutable cell →
      (QuadraticScratchLayout.cellRef cells cell).key ∉ other.storageKeys)
    (avoidsFactor : ∀ cell, QuadraticCheckSeparation.factorKey selection cell ∉ other.storageKeys) :
    QuadraticCandidateSelect.CallerFrameAvoids
      ({ check := QuadraticScratchViews.totalCheckRefs cells candidate, selection := selection } :
        QuadraticCandidateSelect.Refs ctx (QuadraticScratchLayout.ShortWidth N)) other :=
  ⟨⟨avoids .greaterThanOne (by trivial),
      ⟨avoids .candidateWide (by trivial), avoids .belowModulus (by trivial),
        avoids .division (by trivial), avoids .modulusAccepted (by trivial),
        avoids .eligible (by trivial)⟩⟩,
    avoidsFactor .accepted, avoidsFactor .selected, avoidsFactor .available, avoidsFactor .take⟩

private theorem quadraticCallerFrame_of_physical {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}
    (cells : QuadraticScratchLayout.Cells ctx N)
    (shortSelection : FirstAccepted.Direct.Refs ctx (QuadraticScratchLayout.ShortWidth N))
    (selection : FirstAccepted.Refs ctx (QuadraticScratchLayout.CandidateWidth N))
    (other : CInputRef ctx shape)
    (avoids : ∀ cell, IsQuadraticMutable cell →
      (QuadraticScratchLayout.cellRef cells cell).key ∉ other.storageKeys)
    (avoidsFactor : ∀ cell, QuadraticCheckSeparation.factorKey selection cell ∉ other.storageKeys) :
    QuadraticRecoveryGuarded.CallerFrameAvoids
      (QuadraticScratchViews.guardedRefs cells shortSelection selection) other := by
  let shortLog := FirstAccepted.cellRead shortSelection.selected
  let candidates := QuadraticScratchViews.candidateRefs cells shortLog
  exact {
    reset := ⟨avoids .sqrtWideInput (by trivial), avoids .sqrtRoot (by trivial),
      avoids .sqrtHalf (by trivial), avoids .sqrtOutput (by trivial)⟩
    recovery := ⟨quadraticCandidatesFrame cells shortLog other avoids,
      ⟨quadraticSelectFrame cells (QuadraticCandidates.firstCandidate candidates)
          selection other avoids avoidsFactor,
        quadraticSelectFrame cells (QuadraticCandidates.secondCandidate candidates)
          selection other avoids avoidsFactor⟩⟩ }

/-- Physical avoidance supplies the complete pair-factor caller frame. -/
theorem callerFrame_of_physical {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}
    (transport : Transport outer ctx)
    (cells : Cells ctx N)
    (certificates :
      Certificates transport cells)
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
    (avoidsQuadratic : ∀ cell, IsQuadraticMutable cell → ((QuadraticScratchLayout.cellRef
        cells.quadratic cell).toCStorageRef.key ∉ other.storageKeys))
    (avoidsFactor : ∀ cell, ((QuadraticCheckSeparation.factorKey
        (liftSelection transport
          selection) cell) ∉ other.storageKeys)) :
    LatticePairFactorRecovery.CallerFrameAvoids
      (refs transport cells selection firstTerminal secondTerminal parameter)
        other := by
  refine ⟨?_, ?_⟩
  · exact LatticePairCandidateWorkspaceSeparation.callerFrame_of_physical
      transport cells.pair certificates.pair firstTerminal secondTerminal parameter other
        avoidsShared avoidsSlot avoidsState avoidsTarget avoidsLll avoidsNearest
  · exact quadraticCallerFrame_of_physical cells.quadratic
      (LatticeCandidateSlotWorkspaceViews.selectionRefs cells.pair.core.slot)
      (liftSelection transport selection) other avoidsQuadratic avoidsFactor

/-- Physical workspace and persistent-selector facts supply pair-factor separation. -/
theorem separation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : Cells ctx N}
    (certificates :
      Certificates transport cells)
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (selectorSeparated : SelectorSeparation selection)
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticePairFactorRecovery.Separation
      (refs transport cells selection firstTerminal secondTerminal parameter) := by
  let factorSelection := liftSelection transport
    selection
  let shortSelection :=
    LatticeCandidateSlotWorkspaceViews.selectionRefs cells.pair.core.slot
  let candidate := LatticePairCandidateWorkspaceSeparation.refs transport cells.pair
    firstTerminal secondTerminal parameter
  refine {
    pair := LatticePairCandidateWorkspaceSeparation.separation certificates.pair
      firstTerminal secondTerminal parameter
    quadratic := ?_
    modulusFrame := ?_
    firstOneFrame := ?_
    firstModulusFrame := ?_
    firstZeroFrame := ?_
    secondOneFrame := ?_
    secondModulusFrame := ?_
    secondZeroFrame := ?_
    factorAcceptedFrame := ?_
    factorSelectedFrame := ?_ }
  · change QuadraticRecoveryGuarded.Separation
      (QuadraticScratchViews.guardedRefs cells.quadratic shortSelection
        factorSelection)
    exact QuadraticGuardSeparation.guardedSeparation cells.quadratic
      certificates.quadraticDistinct shortSelection
        (shortSelectionSeparation certificates) factorSelection
          (factorSeparation transport cells certificates selection selectorSeparated)
  · change LatticePairCandidateRecovery.CallerFrameAvoids candidate
      (FirstAccepted.cellRead
        (QuadraticScratchLayout.cellRef cells.quadratic .modulus))
    exact candidateFrame_quadraticCell transport cells certificates
      firstTerminal secondTerminal parameter .modulus
  · change LatticePairCandidateRecovery.CallerFrameAvoids candidate
      (FirstAccepted.cellRead
        (QuadraticScratchLayout.cellRef cells.quadratic .one))
    exact candidateFrame_quadraticCell transport cells certificates
      firstTerminal secondTerminal parameter .one
  · change LatticePairCandidateRecovery.CallerFrameAvoids candidate
      (FirstAccepted.cellRead
        (QuadraticScratchLayout.cellRef cells.quadratic .modulus))
    exact candidateFrame_quadraticCell transport cells certificates
      firstTerminal secondTerminal parameter .modulus
  · change LatticePairCandidateRecovery.CallerFrameAvoids candidate
      (FirstAccepted.cellRead
        (QuadraticScratchLayout.cellRef cells.quadratic .zero))
    exact candidateFrame_quadraticCell transport cells certificates
      firstTerminal secondTerminal parameter .zero
  · change LatticePairCandidateRecovery.CallerFrameAvoids candidate
      (FirstAccepted.cellRead
        (QuadraticScratchLayout.cellRef cells.quadratic .one))
    exact candidateFrame_quadraticCell transport cells certificates
      firstTerminal secondTerminal parameter .one
  · change LatticePairCandidateRecovery.CallerFrameAvoids candidate
      (FirstAccepted.cellRead
        (QuadraticScratchLayout.cellRef cells.quadratic .modulus))
    exact candidateFrame_quadraticCell transport cells certificates
      firstTerminal secondTerminal parameter .modulus
  · change LatticePairCandidateRecovery.CallerFrameAvoids candidate
      (FirstAccepted.cellRead
        (QuadraticScratchLayout.cellRef cells.quadratic .zero))
    exact candidateFrame_quadraticCell transport cells certificates
      firstTerminal secondTerminal parameter .zero
  · change LatticePairCandidateRecovery.CallerFrameAvoids candidate
      (QuadraticCheckSeparation.factorInput factorSelection .accepted)
    exact candidateFrame_factorCell transport cells certificates selection
      firstTerminal secondTerminal parameter .accepted
  · change LatticePairCandidateRecovery.CallerFrameAvoids candidate
      (QuadraticCheckSeparation.factorInput factorSelection .selected)
    exact candidateFrame_factorCell transport cells certificates selection
      firstTerminal secondTerminal parameter .selected

end

end LatticePairFactorWorkspaceSeparation
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
