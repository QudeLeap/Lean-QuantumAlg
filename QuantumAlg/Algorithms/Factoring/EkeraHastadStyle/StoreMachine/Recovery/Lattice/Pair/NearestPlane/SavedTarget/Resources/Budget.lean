/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.NearestPlane.SavedTarget.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Input.Program.Resources.Budget
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Program.Resources.Support

/-!
# Independent native budget for saved-target pair reduction

The source-to-LLL allowance precedes the exact three-copy ledger and the
independent allowance for all three nearest-plane stages.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairNearestPlaneSavedTarget

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- Independent native coordinate budget including the three original saved-target copies. -/
def eventEnvelope (N : Nat) : ResourcePool model :=
  LatticeWideLllMachine.eventEnvelope N +
    (ResourcePool.ofList (LatticeRows.pointCopyTrace (LatticeWideLllMachine.Width N)) +
      LatticeNearestPlaneThree.eventEnvelope (LatticeWideLllMachine.Width N))

-- Specializing the three-stage nearest-plane bound elaborates its dependent path.
set_option maxRecDepth 4096 in
/-- Every actual saved-target path satisfies the full independent native coordinate budget. -/
theorem pairToNearestPlaneSavedTargetInto_pool_le (refs : Refs ctx N)
    (path : (pairToNearestPlaneSavedTargetInto refs).Path) :
    (pairToNearestPlaneSavedTargetInto refs).resourcePool path ≤ eventEnvelope N := by
  have source : (LatticeWideLllMachine.pairToLllInto refs.pairNearest.wide).resourcePool path.1 ≤
      LatticeWideLllMachine.eventEnvelope N :=
    LatticeWideLllMachine.pairToLllInto_pool_le refs.pairNearest.wide path.1
  have nearest : (LatticeNearestPlaneThree.threeInto (nearestRefs refs)).resourcePool path.2.2 ≤
      LatticeNearestPlaneThree.eventEnvelope (LatticeWideLllMachine.Width N) :=
    LatticeNearestPlaneThree.threeInto_pool_le (nearestRefs refs) path.2.2
  unfold eventEnvelope
  rw [pairToNearestPlaneSavedTargetInto_resourcePool]
  exact add_le_add source (add_le_add le_rfl nearest)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairNearestPlaneSavedTarget
