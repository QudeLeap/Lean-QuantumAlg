/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Workspace.Separation.Third
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Workspace.Separation.First
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Workspace.Separation.Frames

/-!
# Complete nearest-plane physical separation
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical
namespace LatticeNearestPlaneScratchWorkspaceSeparation

open Execution
open ClassicalRoutines.NumberTheory

noncomputable section

/-- The persistent pair state and one reusable nearest-plane scratch package
satisfy the complete three-stage separation contract. -/
theorem separation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    LatticeNearestPlaneThree.Separation
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch) := by
  let refs := LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
    state scratch
  change LatticeNearestPlaneThree.Separation refs
  refine {
    third := thirdSeparation certificates
    second := secondSeparation certificates
    first := firstSeparation certificates
    secondPreservesThirdOutput := ?_
    firstPreservesThirdOutput := ?_
    firstPreservesSecondOutput := ?_ }
  · exact secondFrameAvoidsWrite certificates refs.third.division.output
      (.inr .thirdOutput) rfl (by intro target; cases target <;> decide)
  · exact firstFrameAvoidsWrite certificates refs.third.division.output
      (.inr .thirdOutput) rfl (by intro target; cases target <;> decide)
  · exact firstFrameAvoidsWrite certificates refs.second.division.output
      (.inr .secondOutput) rfl (by intro target; cases target <;> decide)

end

end LatticeNearestPlaneScratchWorkspaceSeparation
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical
