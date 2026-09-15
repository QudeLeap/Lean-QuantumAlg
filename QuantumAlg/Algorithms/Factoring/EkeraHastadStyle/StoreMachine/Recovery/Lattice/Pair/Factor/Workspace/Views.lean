/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Factor.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Views
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Workspace.Views

/-!
# Physical pair-to-factor recovery view

The pair candidate view shares its short-log selector with guarded quadratic
recovery and retains the supplied persistent factor selector.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical
namespace LatticePairRecoveryWorkspaceViews

open ClassicalRoutines

noncomputable section

/-- Complete pair-to-factor view, sharing both persistent selectors. -/
def factorRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (shared : LatticeCandidateSharedWorkspaceLayout.Cells ctx N)
    (quadratic : QuadraticScratchLayout.Cells ctx N)
    (slot : LatticeCandidateSlotWorkspaceViews.Layout.Cells ctx N)
    (state : LatticePairStateWorkspaceViews.Layout.Cells ctx N)
    (targetScratch : LatticeWideTargetWorkspaceViews.Scratch.Cells ctx N)
    (lllScratch : LatticeFixedFuelScratchWorkspaceViews.Scratch.Cells ctx N)
    (nearestScratch :
      LatticeNearestPlaneScratchWorkspaceViews.Scratch.Cells ctx N)
    (firstTerminal secondTerminal :
      CInputRef ctx (.bits (measurementBits N)))
    (setup : LatticeCandidateModularSetup.Refs ctx N)
    (factorSelection : FirstAccepted.Refs ctx
      (QuadraticScratchLayout.CandidateWidth N)) :
    LatticePairFactorRecovery.Refs ctx N :=
  let pair := candidateRefs shared slot state targetScratch lllScratch
    nearestScratch firstTerminal secondTerminal setup
  let shortSelection := LatticeCandidateSlotWorkspaceViews.selectionRefs slot
  { pair := pair
    quadratic := QuadraticScratchViews.guardedRefs quadratic shortSelection
      factorSelection
    sharedShortLog := rfl }


end

end LatticePairRecoveryWorkspaceViews
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical
