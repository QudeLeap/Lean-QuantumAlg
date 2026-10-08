/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.NearestPlane.SavedTarget.Correctness

/-!
# Actual saved-target nearest-plane native resources

Three actual target copies are charged between the original source-to-LLL run
and the original nearest-plane suffix. The complete selected formula, count,
depth and context bounds include those saved-target storage cells throughout.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairNearestPlaneSavedTarget

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- The actual path composes the verified source, copy and nearest-plane traces in order. -/
theorem pairToNearestPlaneSavedTargetInto_events (refs : Refs ctx N)
    (path : (pairToNearestPlaneSavedTargetInto refs).Path) :
    (pairToNearestPlaneSavedTargetInto refs).eventTrace path =
      (LatticeWideLllMachine.pairToLllInto refs.pairNearest.wide).eventTrace path.1 ++
        (LatticeRows.pointCopyTrace (LatticeWideLllMachine.Width N) ++
          (LatticeNearestPlaneThree.threeInto (nearestRefs refs)).eventTrace path.2.2) :=
  congrArg₂ List.append rfl
    (congrArg₂ List.append
      (LatticeRows.pointCopy_events refs.pairNearest.wide.target.target.point refs.savedTarget
        path.2.1) rfl)

/-- Actual native multiplicities retain the source run, three target copies and nearest plane. -/
theorem pairToNearestPlaneSavedTargetInto_resourcePool (refs : Refs ctx N)
    (path : (pairToNearestPlaneSavedTargetInto refs).Path) :
    (pairToNearestPlaneSavedTargetInto refs).resourcePool path =
      (LatticeWideLllMachine.pairToLllInto refs.pairNearest.wide).resourcePool path.1 +
        (ResourcePool.ofList (LatticeRows.pointCopyTrace (LatticeWideLllMachine.Width N)) +
          (LatticeNearestPlaneThree.threeInto (nearestRefs refs)).resourcePool path.2.2) := by
  change ResourcePool.ofList ((pairToNearestPlaneSavedTargetInto refs).eventTrace path) = _
  rw [pairToNearestPlaneSavedTargetInto_events]
  simp only [ResourcePool.ofList_append]
  rfl

/-- Independent full budget includes exactly three added saved-target word copies. -/
def operationBound (N : Nat) : Nat := LatticeWideLllMachine.operationBound N + 131

/-- The complete actual saved-target path obeys the independent full native operation budget. -/
theorem pairToNearestPlaneSavedTargetInto_eventCount_le (refs : Refs ctx N)
    (path : (pairToNearestPlaneSavedTargetInto refs).Path) :
    ((pairToNearestPlaneSavedTargetInto refs).eventTrace path).length ≤ operationBound N := by
  have wide := LatticeWideLllMachine.pairToLllInto_eventCount_le refs.pairNearest.wide path.1
  have nearest := LatticeNearestPlaneThree.threeInto_eventCount_le (nearestRefs refs) path.2.2
  change List.length (_ ++ (_ ++ _)) ≤ _
  simp only [List.length_append]
  change ((LatticeWideLllMachine.pairToLllInto refs.pairNearest.wide).eventTrace path.1).length +
    (3 + ((LatticeNearestPlaneThree.threeInto (nearestRefs refs)).eventTrace path.2.2).length) ≤
      LatticeWideLllMachine.operationBound N + 131
  omega

/-- Complete unit-duration depth charges saved-target copying before nearest-plane computation. -/
theorem pairToNearestPlaneSavedTargetInto_depth_le (refs : Refs ctx N)
    (path : (pairToNearestPlaneSavedTargetInto refs).Path) :
    (pairToNearestPlaneSavedTargetInto refs).depth (fun _ => 1) path ≤ operationBound N := by
  have wide := LatticeWideLllMachine.pairToLllInto_depth_le refs.pairNearest.wide path.1
  have nearest := LatticeNearestPlaneThree.threeInto_depth_le (nearestRefs refs) path.2.2
  change (LatticeWideLllMachine.pairToLllInto refs.pairNearest.wide).depth (fun _ => 1) path.1 +
    (3 + (LatticeNearestPlaneThree.threeInto (nearestRefs refs)).depth (fun _ => 1) path.2.2) ≤
      LatticeWideLllMachine.operationBound N + 131
  omega

/-- Actual copying and nearest plane preserve every original borrowed-reference correlation. -/
theorem copyNearestInto_borrowedRestored (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (copyNearestInto refs).BorrowedRestored Reference state
      ((copyNearestInto refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (LatticeRows.pointCopy_borrowedRestored refs.pairNearest.wide.target.target.point
      refs.savedTarget
      Reference state)
    (LatticeNearestPlaneThree.threeInto_borrowedRestored (nearestRefs refs) Reference _)

/-- The complete actual saved-target run restores every borrowed-reference joint state. -/
theorem pairToNearestPlaneSavedTargetInto_borrowedRestored (refs : Refs ctx N)
    (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pairToNearestPlaneSavedTargetInto refs).BorrowedRestored Reference state
      ((pairToNearestPlaneSavedTargetInto refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (LatticeWideLllMachine.pairToLllInto_borrowedRestored refs.pairNearest.wide Reference state)
    (copyNearestInto_borrowedRestored refs Reference _)

/-- Every actual copy and nearest-plane instruction retains the complete original context. -/
theorem copyNearestInto_visited (refs : Refs ctx N) (path : (copyNearestInto refs).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (copyNearestInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (_ ++ _) at present
  exact (List.mem_append.mp present).elim
    (by
      intro copied
      have member : visited ∈ List.replicate 3 ctx := by
        simpa only [copyInto, LatticeRows.pointCopy_visited] using copied
      exact (List.mem_replicate.mp member).2)
    (LatticeNearestPlaneThree.threeInto_visited (nearestRefs refs) path.2 visited)

/-- Every actual source, copy and nearest-plane instruction retains all original context entries. -/
theorem pairToNearestPlaneSavedTargetInto_visited (refs : Refs ctx N)
    (path : (pairToNearestPlaneSavedTargetInto refs).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (pairToNearestPlaneSavedTargetInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (_ ++ _) at present
  exact (List.mem_append.mp present).elim
    (LatticeWideLllMachine.pairToLllInto_visited refs.pairNearest.wide path.1 visited)
    (copyNearestInto_visited refs path.2 visited)

/-- Resident accounting retains all original cells, including the independent saved target. -/
theorem pairToNearestPlaneSavedTargetInto_resident_le (refs : Refs ctx N)
    (path : (pairToNearestPlaneSavedTargetInto refs).Path) :
    (pairToNearestPlaneSavedTargetInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [pairToNearestPlaneSavedTargetInto_visited refs path visited present]

/-- Auxiliary accounting retains all original roles, including every saved-target workspace word. -/
theorem pairToNearestPlaneSavedTargetInto_auxiliary_le (refs : Refs ctx N)
    (path : (pairToNearestPlaneSavedTargetInto refs).Path) :
    (pairToNearestPlaneSavedTargetInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [pairToNearestPlaneSavedTargetInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairNearestPlaneSavedTarget
