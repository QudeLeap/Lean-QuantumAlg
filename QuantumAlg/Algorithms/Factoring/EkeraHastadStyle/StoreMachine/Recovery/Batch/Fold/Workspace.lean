/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Pairs
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Reusable.Workspace.Separation

/-!
# Physical references for the reusable pair fold

This module indexes one reusable physical pair workspace by the canonical
unordered pairs of sixteen retained terminal cells.  It proves that structural
transport commutes with the pair enumeration and closes the fold alignment.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticePairRecoveryFoldWorkspace

open Execution
open Execution.ClassicalWorkspace
open ClassicalRoutines

noncomputable section

/-- Transport all retained terminal cells into the reusable pair scope. -/
def liftTerminals {kind : ProblemKind} {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (terminals : LatticePairRecoveryBatch.Terminals outer N) :
    LatticePairRecoveryBatch.Terminals ctx N :=
  fun index => transport.liftInput (terminals index)

/-- Transport commutes with the canonical unordered-pair enumeration. -/
lemma terminalPairs_lift {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (terminals : LatticePairRecoveryBatch.Terminals outer N) :
    LatticePairRecoveryBatch.terminalPairs
        (liftTerminals transport terminals) =
      (LatticePairRecoveryBatch.terminalPairs terminals).map fun pair =>
        (transport.liftInput pair.1, transport.liftInput pair.2) := by
  unfold LatticePairRecoveryFold.PairCount
  have terminalsLift :
      List.Vector.ofFn (liftTerminals transport terminals) =
        (List.Vector.ofFn terminals).map transport.liftInput := by
    apply List.Vector.ext
    intro index
    simp only [List.Vector.get_ofFn, List.Vector.get_map, liftTerminals]
  unfold LatticePairRecoveryBatch.terminalPairs
  rw [terminalsLift]
  apply List.Vector.toList_injective
  rw [List.Vector.toList_unorderedPairs_map, List.Vector.toList_map]

/-- One physical pair workspace viewed at every canonical terminal pair. -/
def refs {kind : ProblemKind} {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : LatticePairFactorWorkspaceSeparation.Cells ctx N)
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (terminals : LatticePairRecoveryBatch.Terminals outer N)
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticePairRecoveryFold.Refs ctx N where
  pair index :=
    let pair := (LatticePairRecoveryBatch.terminalPairs terminals).get index
    LatticePairFactorWorkspaceSeparation.refs transport cells selection pair.1 pair.2
      parameter
  factorSelection := LatticePairFactorWorkspaceSeparation.liftSelection transport
    selection
  sharedFactorSelection _ := rfl

/-- The indexed physical views read exactly the transported terminal pairs. -/
lemma aligned {kind : ProblemKind} {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : LatticePairFactorWorkspaceSeparation.Cells ctx N)
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (terminals : LatticePairRecoveryBatch.Terminals outer N)
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticePairRecoveryBatch.Aligned
      (refs transport cells selection terminals parameter)
      (liftTerminals transport terminals) := by
  constructor
  · intro index
    change transport.liftInput
        ((LatticePairRecoveryBatch.terminalPairs terminals).get index).1 = _
    rw [terminalPairs_lift]
    simp only [List.Vector.get_map]
  · intro index
    change transport.liftInput
        ((LatticePairRecoveryBatch.terminalPairs terminals).get index).2 = _
    rw [terminalPairs_lift]
    simp only [List.Vector.get_map]

/-- Outer parameter and terminal cells avoid the persistent factor selector. -/
structure FactorFrameAvoids {kind : ProblemKind}
    {outer : RuntimeCtx kind} {N : Nat}
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (terminals : LatticePairRecoveryBatch.Terminals outer N)
    (parameter : CInputRef outer (ParameterShape N)) : Prop where
  parameter : ∀ cell, QuadraticCheckSeparation.factorKey selection cell ∉ parameter.storageKeys
  first : ∀ index cell, QuadraticCheckSeparation.factorKey selection cell ∉
    ((LatticePairRecoveryBatch.terminalPairs terminals).get index).1.storageKeys
  second : ∀ index cell, QuadraticCheckSeparation.factorKey selection cell ∉
    ((LatticePairRecoveryBatch.terminalPairs terminals).get index).2.storageKeys

private lemma storageRead_not_mem {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} {source : CStorageRef ctx shape} {key : StorageKey}
    (different : source.key ≠ key) : key ∉ (CInputRef.storage source).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton, ne_comm] using different

private lemma callerFrame_of_outerProjection {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat} {outerShape shape : CShape}
    (transport : Transport outer ctx)
    (cells : LatticePairFactorWorkspaceSeparation.Cells ctx N)
    (certificates :
      LatticePairFactorWorkspaceSeparation.Certificates transport cells)
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N))
    (outerInput : CInputRef outer outerShape) (other : CInputRef ctx shape)
    (projection : ∀ key, key ∉ (transport.liftInput outerInput).storageKeys →
      key ∉ other.storageKeys)
    (factorAvoids : ∀ cell, QuadraticCheckSeparation.factorKey selection cell ∉
      outerInput.storageKeys) :
    LatticePairReusableRecovery.CallerFrameAvoids
      (LatticePairFactorWorkspaceSeparation.refs transport cells selection
        firstTerminal secondTerminal parameter) other := by
  apply LatticePairReusableWorkspaceSeparation.callerFrame_of_physical
    transport cells certificates selection firstTerminal secondTerminal parameter other
  · intro cell
    exact projection _
      (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids cells.pair.core.shared
        transport certificates.pair.core.sharedSeparated outerInput cell)
  · intro cell
    apply projection
    simpa only [LatticeCandidateSlotWorkspaceLayout.cellRef_key] using
      (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids cells.pair.core.slot
        transport certificates.pair.core.slotSeparated outerInput
          (LatticeCandidateSlotWorkspaceLayout.cellIndex N cell))
  · intro cell
    apply projection
    simpa only [LatticePairStateWorkspaceLayout.cellRef_key] using
      (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids cells.pair.core.state
        transport certificates.pair.core.stateSeparated outerInput
          (LatticePairStateWorkspaceLayout.cellIndex N cell))
  · intro cell
    apply projection
    simpa only [LatticeWideTargetWorkspaceLayout.cellRef_key] using
      (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids cells.pair.target transport
        certificates.pair.targetSeparated outerInput
          (LatticeWideTargetWorkspaceLayout.cellIndex N cell))
  · intro cell
    apply projection
    simpa only [LatticeFixedFuelScratchWorkspaceLayout.cellRef_key] using
      (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids cells.pair.lll transport
        certificates.pair.lllSeparated outerInput
          (LatticeFixedFuelScratchWorkspaceLayout.cellIndex N cell))
  · intro cell
    apply projection
    simpa only [LatticeNearestPlaneScratchWorkspaceLayout.cellRef_key] using
      (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids cells.pair.nearest transport
        certificates.pair.nearestSeparated outerInput
          (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N cell))
  · intro cell _mutable
    apply projection
    simpa only [QuadraticScratchLayout.cellRef_key] using
      (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids cells.quadratic transport
        certificates.quadraticSeparated outerInput
          (QuadraticScratchLayout.cellIndex N cell))
  · intro cell
    apply projection
    rw [LatticePairFactorWorkspaceSeparation.factorKey_liftSelection,
      transport.liftInput_storageKeys]
    exact factorAvoids cell

/-- An outer input avoids the complete reusable pair under transport. -/
lemma callerFrame_of_outerInput {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}
    (transport : Transport outer ctx)
    (cells : LatticePairFactorWorkspaceSeparation.Cells ctx N)
    (certificates :
      LatticePairFactorWorkspaceSeparation.Certificates transport cells)
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N))
    (other : CInputRef outer shape)
    (factorAvoids : ∀ cell, QuadraticCheckSeparation.factorKey selection cell ∉
      other.storageKeys) :
    LatticePairReusableRecovery.CallerFrameAvoids
      (LatticePairFactorWorkspaceSeparation.refs transport cells selection
        firstTerminal secondTerminal parameter)
      (transport.liftInput other) :=
  callerFrame_of_outerProjection transport cells certificates selection firstTerminal
    secondTerminal parameter other (transport.liftInput other)
      (fun _ avoids => avoids) factorAvoids

private lemma callerFrame_quadraticCell {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (cells : LatticePairFactorWorkspaceSeparation.Cells ctx N)
    (certificates :
      LatticePairFactorWorkspaceSeparation.Certificates transport cells)
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (firstTerminal secondTerminal :
      CInputRef outer (.bits (measurementBits N)))
    (parameter : CInputRef outer (ParameterShape N))
    (source : QuadraticScratchLayout.Cell)
    (immutable : ¬ LatticePairFactorWorkspaceSeparation.IsQuadraticMutable
      source) :
    LatticePairReusableRecovery.CallerFrameAvoids
      (LatticePairFactorWorkspaceSeparation.refs transport cells selection
        firstTerminal secondTerminal parameter)
      (FirstAccepted.cellRead
        (QuadraticScratchLayout.cellRef cells.quadratic source)) := by
  apply LatticePairReusableWorkspaceSeparation.callerFrame_of_physical
    transport cells certificates selection firstTerminal secondTerminal parameter
    (FirstAccepted.cellRead (QuadraticScratchLayout.cellRef cells.quadratic source))
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
  · intro cell mutable
    apply storageRead_not_mem
    intro equal
    apply immutable
    rw [QuadraticScratchLayout.cellRef_key_injective
      cells.quadratic certificates.quadraticDistinct equal]
    exact mutable
  · intro cell
    apply storageRead_not_mem
    have factorAvoidsSource : (QuadraticScratchLayout.cellRef cells.quadratic source).key ∉
        (QuadraticCheckSeparation.factorInput
          (LatticePairFactorWorkspaceSeparation.liftSelection transport selection)
            cell).storageKeys := by
      rw [LatticePairFactorWorkspaceSeparation.factorInput_liftSelection]
      simpa only [QuadraticScratchLayout.cellRef_key] using
        (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids cells.quadratic
          transport certificates.quadraticSeparated
            (QuadraticCheckSeparation.factorInput selection cell)
            (QuadraticScratchLayout.cellIndex N source))
    have factorDifferent :
        QuadraticCheckSeparation.factorKey
            (LatticePairFactorWorkspaceSeparation.liftSelection transport selection) cell ≠
          (QuadraticScratchLayout.cellRef cells.quadratic source).key := by
      cases cell <;> simpa only [QuadraticCheckSeparation.factorKey,
        QuadraticCheckSeparation.factorInput, FirstAccepted.cellRead,
        CInputRef.storageKeys, List.mem_singleton, ne_comm] using factorAvoidsSource
    exact factorDifferent.symm

/-- One reusable physical allocation supplies every pair in the fixed fold. -/
lemma separation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairFactorWorkspaceSeparation.Cells ctx N}
    (certificates :
      LatticePairFactorWorkspaceSeparation.Certificates transport cells)
    (selection : FirstAccepted.Refs outer (QuadraticScratchLayout.CandidateWidth N))
    (selectorSeparated : LatticePairFactorWorkspaceSeparation.SelectorSeparation selection)
    (terminals : LatticePairRecoveryBatch.Terminals outer N)
    (parameter : CInputRef outer (ParameterShape N))
    (factorFrames : FactorFrameAvoids selection terminals parameter) :
    LatticePairRecoveryFold.Separation
      (refs transport cells selection terminals parameter) := by
  refine {
    each := ?_
    initialFrames := ?_
    sourceFrames := ?_ }
  · intro index
    let pair := (LatticePairRecoveryBatch.terminalPairs terminals).get index
    change LatticePairReusableRecovery.Separation
      (LatticePairFactorWorkspaceSeparation.refs transport cells selection pair.1
        pair.2 parameter)
    exact LatticePairReusableWorkspaceSeparation.separation certificates selection
      selectorSeparated pair.1 pair.2 parameter
  · intro current target
    let currentPair :=
      (LatticePairRecoveryBatch.terminalPairs terminals).get current
    let targetPair :=
      (LatticePairRecoveryBatch.terminalPairs terminals).get target
    change LatticePairRecoveryFold.InitialFrameAvoids
      (LatticePairFactorWorkspaceSeparation.refs transport cells selection
        currentPair.1 currentPair.2 parameter)
      (LatticePairFactorWorkspaceSeparation.refs transport cells selection
        targetPair.1 targetPair.2 parameter)
    refine {
      setupParameter := ?_
      setupBase := ?_
      quadraticModulus := ?_
      firstOne := ?_
      firstModulus := ?_
      firstZero := ?_
      secondOne := ?_
      secondModulus := ?_
      secondZero := ?_ }
    · exact callerFrame_of_outerInput transport cells certificates selection
        currentPair.1 currentPair.2 parameter parameter factorFrames.parameter
    · change LatticePairReusableRecovery.CallerFrameAvoids
        (LatticePairFactorWorkspaceSeparation.refs transport cells selection
          currentPair.1 currentPair.2 parameter)
        (CInputRef.first (transport.liftInput parameter))
      exact callerFrame_of_outerProjection transport cells certificates selection
        currentPair.1 currentPair.2 parameter parameter
          (CInputRef.first (transport.liftInput parameter))
            (fun _ avoided => avoided) factorFrames.parameter
    · exact callerFrame_quadraticCell transport cells certificates selection
        currentPair.1 currentPair.2 parameter .modulus
          (by simp [LatticePairFactorWorkspaceSeparation.IsQuadraticMutable])
    · exact callerFrame_quadraticCell transport cells certificates selection
        currentPair.1 currentPair.2 parameter .one
          (by simp [LatticePairFactorWorkspaceSeparation.IsQuadraticMutable])
    · exact callerFrame_quadraticCell transport cells certificates selection
        currentPair.1 currentPair.2 parameter .modulus
          (by simp [LatticePairFactorWorkspaceSeparation.IsQuadraticMutable])
    · exact callerFrame_quadraticCell transport cells certificates selection
        currentPair.1 currentPair.2 parameter .zero
          (by simp [LatticePairFactorWorkspaceSeparation.IsQuadraticMutable])
    · exact callerFrame_quadraticCell transport cells certificates selection
        currentPair.1 currentPair.2 parameter .one
          (by simp [LatticePairFactorWorkspaceSeparation.IsQuadraticMutable])
    · exact callerFrame_quadraticCell transport cells certificates selection
        currentPair.1 currentPair.2 parameter .modulus
          (by simp [LatticePairFactorWorkspaceSeparation.IsQuadraticMutable])
    · exact callerFrame_quadraticCell transport cells certificates selection
        currentPair.1 currentPair.2 parameter .zero
          (by simp [LatticePairFactorWorkspaceSeparation.IsQuadraticMutable])
  · intro current target
    let currentPair :=
      (LatticePairRecoveryBatch.terminalPairs terminals).get current
    let targetPair :=
      (LatticePairRecoveryBatch.terminalPairs terminals).get target
    change LatticePairRecoveryFold.SourceFrameAvoids
      (LatticePairFactorWorkspaceSeparation.refs transport cells selection
        currentPair.1 currentPair.2 parameter)
      (LatticePairFactorWorkspaceSeparation.refs transport cells selection
        targetPair.1 targetPair.2 parameter)
    constructor
    · intro index
      change LatticePairReusableRecovery.CallerFrameAvoids
        (LatticePairFactorWorkspaceSeparation.refs transport cells selection
          currentPair.1 currentPair.2 parameter)
        (.bitsGet (transport.liftInput targetPair.1) index)
      exact callerFrame_of_outerProjection transport cells certificates selection
        currentPair.1 currentPair.2 parameter targetPair.1
          (.bitsGet (transport.liftInput targetPair.1) index)
            (fun _ avoided => avoided) (factorFrames.first target)
    · intro index
      change LatticePairReusableRecovery.CallerFrameAvoids
        (LatticePairFactorWorkspaceSeparation.refs transport cells selection
          currentPair.1 currentPair.2 parameter)
        (.bitsGet (transport.liftInput targetPair.2) index)
      exact callerFrame_of_outerProjection transport cells certificates selection
        currentPair.1 currentPair.2 parameter targetPair.2
          (.bitsGet (transport.liftInput targetPair.2) index)
            (fun _ avoided => avoided) (factorFrames.second target)

end

end LatticePairRecoveryFoldWorkspace
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
