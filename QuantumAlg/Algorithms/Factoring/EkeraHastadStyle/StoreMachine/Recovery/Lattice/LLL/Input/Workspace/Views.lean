/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Input.Program.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Wide.Workspace.Views
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Workspace.Views

/-!
# Physical wide pair-to-LLL component view

This module joins the persistent pair state, wide-target scratch, and reusable
fixed-fuel scratch into the exact `LatticeWideLllMachine.Refs` package.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeWideLllWorkspaceViews

noncomputable section

/-- Exact pair-to-LLL view over the three physical workspace inventories. -/
def wideRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceViews.Layout.Cells ctx N)
    (targetScratch : LatticeWideTargetWorkspaceViews.Scratch.Cells ctx N)
    (lllScratch : LatticeFixedFuelScratchWorkspaceViews.Scratch.Cells ctx N)
    (pair : BatchMachine.PairRefs ctx N) : LatticeWideLllMachine.Refs ctx N where
  initialization :=
    LatticeFixedFuelScratchWorkspaceViews.initializationRefs state lllScratch pair
  target := LatticeWideTargetWorkspaceViews.targetRefs state targetScratch pair
  firstTargetK := rfl
  secondTargetK := rfl
  targetModulus := rfl
  targetPoint := rfl

end

end LatticeWideLllWorkspaceViews
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
