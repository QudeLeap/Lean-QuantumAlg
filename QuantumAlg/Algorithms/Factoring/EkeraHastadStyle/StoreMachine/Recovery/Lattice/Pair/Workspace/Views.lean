/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Workspace.Views
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Workspace.Views
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Shared.Workspace.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Program.Layout

/-!
# Physical pair and candidate recovery views

Previously allocated cell packages supply the actual pair-reduction and
candidate-scan references. The three nearest-plane outputs keep their original
workspace roles, and every component receives its original cells.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticePairRecoveryWorkspaceViews

open ClassicalRoutines

noncomputable section

/-- Pair reduction and nearest-plane references over the physical state and
phase-local scratch packages. -/
def pairRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceViews.Layout.Cells ctx N)
    (targetScratch : LatticeWideTargetWorkspaceViews.Scratch.Cells ctx N)
    (lllScratch : LatticeFixedFuelScratchWorkspaceViews.Scratch.Cells ctx N)
    (nearestScratch :
      LatticeNearestPlaneScratchWorkspaceViews.Scratch.Cells ctx N)
    (firstTerminal secondTerminal :
      CInputRef ctx (.bits (measurementBits N))) :
    LatticePairNearestPlaneSavedTarget.Refs ctx N where
  pairNearest := LatticeNearestPlaneScratchWorkspaceViews.pairRefs state
    targetScratch lllScratch nearestScratch
      (LatticePairStateWorkspaceViews.pairRefs state firstTerminal secondTerminal)
  savedTarget := LatticePairStateWorkspaceViews.savedTargetRefs state

/-- The three nearest-plane quotient outputs are workspace-owned. -/
theorem nearestOutputRoles {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceViews.Layout.Cells ctx N)
    (targetScratch : LatticeWideTargetWorkspaceViews.Scratch.Cells ctx N)
    (lllScratch : LatticeFixedFuelScratchWorkspaceViews.Scratch.Cells ctx N)
    (nearestScratch :
      LatticeNearestPlaneScratchWorkspaceViews.Scratch.Cells ctx N)
    (firstTerminal secondTerminal :
      CInputRef ctx (.bits (measurementBits N))) :
    LatticeCandidateSlotWorkspaceViews.NearestOutputRoles
      (pairRefs state targetScratch lllScratch nearestScratch
        firstTerminal secondTerminal) where
  first := by
    change
      (LatticeNearestPlaneScratchWorkspaceLayout.cellRef nearestScratch
        .targetDotSecond).toCStorageRef.role = .workspace
    exact LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role
      nearestScratch .targetDotSecond
  second := by
    change
      (LatticeNearestPlaneScratchWorkspaceLayout.cellRef nearestScratch
        .secondOutput).toCStorageRef.role = .workspace
    exact LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role
      nearestScratch .secondOutput
  third := by
    change
      (LatticeNearestPlaneScratchWorkspaceLayout.cellRef nearestScratch
        .thirdOutput).toCStorageRef.role = .workspace
    exact LatticeNearestPlaneScratchWorkspaceLayout.cellRef_role
      nearestScratch .thirdOutput

/-- Complete pair-to-short-log recovery view over all reusable physical cells. -/
def candidateRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (shared : LatticeCandidateSharedWorkspaceLayout.Cells ctx N)
    (slot : LatticeCandidateSlotWorkspaceViews.Layout.Cells ctx N)
    (state : LatticePairStateWorkspaceViews.Layout.Cells ctx N)
    (targetScratch : LatticeWideTargetWorkspaceViews.Scratch.Cells ctx N)
    (lllScratch : LatticeFixedFuelScratchWorkspaceViews.Scratch.Cells ctx N)
    (nearestScratch :
      LatticeNearestPlaneScratchWorkspaceViews.Scratch.Cells ctx N)
    (firstTerminal secondTerminal :
      CInputRef ctx (.bits (measurementBits N)))
    (setup : LatticeCandidateModularSetup.Refs ctx N) :
    LatticePairCandidateRecovery.Refs ctx N :=
  let pair := pairRefs state targetScratch lllScratch nearestScratch
    firstTerminal secondTerminal
  let roles := nearestOutputRoles state targetScratch lllScratch nearestScratch
    firstTerminal secondTerminal
  let constants := LatticeCandidateSharedWorkspaceLayout.constantRefs shared
  let scan := LatticeCandidateSlotWorkspaceViews.slotRefs slot pair roles
    constants setup
  { pair := pair
    constants := constants
    setup := setup
    scan := scan
    scanNearest := rfl
    scanOriginalTarget := rfl
    scanZero := rfl
    scanUpperBound := rfl
    scanModulus := rfl
    scanGenerator := rfl
    scanTargetPower := rfl }


end

end LatticePairRecoveryWorkspaceViews
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
