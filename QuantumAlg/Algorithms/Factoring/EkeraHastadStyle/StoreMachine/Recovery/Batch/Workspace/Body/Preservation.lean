/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Body.Frames
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Reusable.Workspace.Separation

/-!
# Complete caller frame from actual batch allocation certificates

Every persistent top destination and every cell in the seven reusable scratch
packages is fresh for the original caller. The complete recovery body therefore
preserves any caller input whose structural read avoids the final result cell.
No caller initialization or additional physical disjointness is required.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspaceBody

open Execution
open Execution.ClassicalWorkspace
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {root topCtx inner : RuntimeCtx kind} {N : Nat}

private theorem topCell_avoids_rootInput (refs : Refs root topCtx inner N)
    (separation : Separation refs) {shape : CShape} (other : CInputRef root shape)
    (index : Fin (LatticeBatchRecoveryWorkspaceLayout.topShapes N).length) :
    (cellAt (LatticeBatchRecoveryWorkspaceViews.topAt refs.pairTransport refs.top) index).ref.key ∉
      ((refs.topTransport.compose refs.pairTransport).liftInput other).storageKeys :=
  Cells.workspaceCells_cellAt_transport_avoids
    (LatticeBatchRecoveryWorkspaceViews.topAt refs.pairTransport refs.top)
    (refs.topTransport.compose refs.pairTransport)
    (LatticeBatchRecoveryWorkspaceViews.topAt_separated refs.topTransport refs.pairTransport
      refs.top separation.topSeparated) other index

private theorem factorCell_avoids_rootInput (refs : Refs root topCtx inner N)
    (separation : Separation refs) {shape : CShape} (other : CInputRef root shape)
    (cell : QuadraticCheckSeparation.FactorCell) :
    QuadraticCheckSeparation.factorKey
        (LatticePairFactorWorkspaceSeparation.liftSelection refs.pairTransport
          (LatticeBatchRecoveryWorkspaceLayout.factorSelection refs.top)) cell ∉
      ((refs.topTransport.compose refs.pairTransport).liftInput other).storageKeys := by
  rw [← LatticeBatchRecoveryWorkspaceViews.factorSelection_topAt]
  cases cell with
  | accepted =>
      exact topCell_avoids_rootInput refs separation other
        (LatticeBatchRecoveryWorkspaceLayout.acceptedIndex N)
  | selected =>
      exact topCell_avoids_rootInput refs separation other
        (LatticeBatchRecoveryWorkspaceLayout.selectedIndex N)
  | available =>
      exact topCell_avoids_rootInput refs separation other
        (LatticeBatchRecoveryWorkspaceLayout.availableIndex N)
  | take =>
      exact topCell_avoids_rootInput refs separation other
        (LatticeBatchRecoveryWorkspaceLayout.takeIndex N)

private theorem seedCallerFrame (refs : Refs root topCtx inner N)
    (separation : Separation refs) {shape : CShape} (other : CInputRef root shape) :
    LatticeEarlyFactorSeed.CallerFrameAvoids (endpointRefs refs).tail.seed
      ((refs.topTransport.compose refs.pairTransport).liftInput other) where
  wideCandidate := topCell_avoids_rootInput refs separation other
    (LatticeBatchRecoveryWorkspaceLayout.wideIndex N)
  accepted := topCell_avoids_rootInput refs separation other
    (LatticeBatchRecoveryWorkspaceLayout.acceptedIndex N)
  selected := topCell_avoids_rootInput refs separation other
    (LatticeBatchRecoveryWorkspaceLayout.selectedIndex N)
  available := topCell_avoids_rootInput refs separation other
    (LatticeBatchRecoveryWorkspaceLayout.availableIndex N)
  take := topCell_avoids_rootInput refs separation other
    (LatticeBatchRecoveryWorkspaceLayout.takeIndex N)

private theorem pairCallerFrame (refs : Refs root topCtx inner N)
    (separation : Separation refs) {shape : CShape} (other : CInputRef root shape)
    (firstTerminal secondTerminal : CInputRef topCtx (.bits (measurementBits N))) :
    LatticePairReusableRecovery.CallerFrameAvoids
      (LatticePairFactorWorkspaceSeparation.refs refs.pairTransport refs.cells
        (LatticeBatchRecoveryWorkspaceLayout.factorSelection refs.top)
        firstTerminal secondTerminal (refs.topTransport.liftInput refs.parameter))
      ((refs.topTransport.compose refs.pairTransport).liftInput other) := by
  have freshAvoids {shapes : List CShape} (cells : ClassicalWorkspace.Cells inner shapes)
      (separated : cells.TransportSeparated refs.pairTransport) (index : Fin shapes.length) :
      (cellAt cells index).ref.key ∉
        ((refs.topTransport.compose refs.pairTransport).liftInput other).storageKeys := by
    simpa only [Transport.liftInput_compose] using
      Cells.workspaceCells_cellAt_transport_avoids cells refs.pairTransport separated
        (refs.topTransport.liftInput other) index
  apply LatticePairReusableWorkspaceSeparation.callerFrame_of_physical refs.pairTransport
    refs.cells separation.cells (LatticeBatchRecoveryWorkspaceLayout.factorSelection refs.top)
    firstTerminal secondTerminal (refs.topTransport.liftInput refs.parameter)
    ((refs.topTransport.compose refs.pairTransport).liftInput other)
  · exact freshAvoids refs.cells.pair.core.shared separation.cells.pair.core.sharedSeparated
  · intro cell
    simpa only [LatticeCandidateSlotWorkspaceLayout.cellRef_key] using
      freshAvoids refs.cells.pair.core.slot separation.cells.pair.core.slotSeparated
        (LatticeCandidateSlotWorkspaceLayout.cellIndex N cell)
  · intro cell
    simpa only [LatticePairStateWorkspaceLayout.cellRef_key] using
      freshAvoids refs.cells.pair.core.state separation.cells.pair.core.stateSeparated
        (LatticePairStateWorkspaceLayout.cellIndex N cell)
  · intro cell
    simpa only [LatticeWideTargetWorkspaceLayout.cellRef_key] using
      freshAvoids refs.cells.pair.target separation.cells.pair.targetSeparated
        (LatticeWideTargetWorkspaceLayout.cellIndex N cell)
  · intro cell
    simpa only [LatticeFixedFuelScratchWorkspaceLayout.cellRef_key] using
      freshAvoids refs.cells.pair.lll separation.cells.pair.lllSeparated
        (LatticeFixedFuelScratchWorkspaceLayout.cellIndex N cell)
  · intro cell
    simpa only [LatticeNearestPlaneScratchWorkspaceLayout.cellRef_key] using
      freshAvoids refs.cells.pair.nearest separation.cells.pair.nearestSeparated
        (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N cell)
  · intro cell _mutable
    simpa only [QuadraticScratchLayout.cellRef_key] using
      freshAvoids refs.cells.quadratic separation.cells.quadraticSeparated
        (QuadraticScratchLayout.cellIndex N cell)
  · exact factorCell_avoids_rootInput refs separation other

/-- Fresh allocation frames every caller input avoiding the single caller-visible result write. -/
theorem callerFrame_of_rootInput (refs : Refs root topCtx inner N)
    (separation : Separation refs) {shape : CShape} (other : CInputRef root shape)
    (resultAvoids : refs.result.key ∉
      ((refs.topTransport.compose refs.pairTransport).liftInput other).storageKeys) :
    CallerFrameAvoids refs ((refs.topTransport.compose refs.pairTransport).liftInput other) := by
  refine ⟨initializationCallerFrame_of_rootInput refs separation other, ?_⟩
  refine ⟨⟨seedCallerFrame refs separation other, ?_⟩, ?_⟩
  · intro index
    exact pairCallerFrame refs separation other _ _
  · exact ⟨topCell_avoids_rootInput refs separation other
      (LatticeBatchRecoveryWorkspaceLayout.narrowIndex N), resultAvoids⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspaceBody
