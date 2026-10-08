/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.NearestPlane.Program.Correctness

/-!
# Actual source-to-nearest-plane native resources

The original source-to-LLL budget is followed by at most 128 native nearest-
plane instructions. The verified component traces compose in chronological
order; their explicit independent count bounds establish the complete budget.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairNearestPlaneMachine

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- The actual path composes both verified component traces in chronological order. -/
theorem pairToNearestPlaneInto_events (refs : Refs ctx N)
    (path : (pairToNearestPlaneInto refs).Path) :
    (pairToNearestPlaneInto refs).eventTrace path =
      (LatticeWideLllMachine.pairToLllInto refs.wide).eventTrace path.1 ++
        (LatticeNearestPlaneThree.threeInto (nearestRefs refs)).eventTrace path.2 := rfl

/-- The actual complete native multiplicity is the sum of the two actual component pools. -/
theorem pairToNearestPlaneInto_resourcePool (refs : Refs ctx N)
    (path : (pairToNearestPlaneInto refs).Path) :
    (pairToNearestPlaneInto refs).resourcePool path =
      (LatticeWideLllMachine.pairToLllInto refs.wide).resourcePool path.1 +
        (LatticeNearestPlaneThree.threeInto (nearestRefs refs)).resourcePool path.2 :=
  ResourcePool.ofList_append _ _

/-- Independent total budget for original source-to-LLL execution and the nearest-plane suffix. -/
def operationBound (N : Nat) : Nat := LatticeWideLllMachine.operationBound N + 128

/-- Every actual source-to-nearest-plane path obeys the independent full native operation bound. -/
theorem pairToNearestPlaneInto_eventCount_le (refs : Refs ctx N)
    (path : (pairToNearestPlaneInto refs).Path) :
    ((pairToNearestPlaneInto refs).eventTrace path).length ≤ operationBound N := by
  change List.length (_ ++ _) ≤ _
  rw [List.length_append]
  exact Nat.add_le_add (LatticeWideLllMachine.pairToLllInto_eventCount_le refs.wide path.1)
    (LatticeNearestPlaneThree.threeInto_eventCount_le (nearestRefs refs) path.2)

/-- Actual unit-duration depth includes the dependence of nearest plane on original LLL output. -/
theorem pairToNearestPlaneInto_depth_le (refs : Refs ctx N)
    (path : (pairToNearestPlaneInto refs).Path) :
    (pairToNearestPlaneInto refs).depth (fun _ => 1) path ≤ operationBound N :=
  Nat.add_le_add (LatticeWideLllMachine.pairToLllInto_depth_le refs.wide path.1)
    (LatticeNearestPlaneThree.threeInto_depth_le (nearestRefs refs) path.2)

/-- The complete actual original-sample run restores every borrowed-reference joint state. -/
theorem pairToNearestPlaneInto_borrowedRestored (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pairToNearestPlaneInto refs).BorrowedRestored Reference state
      ((pairToNearestPlaneInto refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (LatticeWideLllMachine.pairToLllInto_borrowedRestored refs.wide Reference state)
    (LatticeNearestPlaneThree.threeInto_borrowedRestored (nearestRefs refs) Reference _)

/-- Every actual original-sample instruction retains the complete originally supplied context. -/
theorem pairToNearestPlaneInto_visited (refs : Refs ctx N)
    (path : (pairToNearestPlaneInto refs).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (pairToNearestPlaneInto refs).visitedContexts path) : visited = ctx := by
  change visited ∈ (_ ++ _) at present
  exact (List.mem_append.mp present).elim
    (LatticeWideLllMachine.pairToLllInto_visited refs.wide path.1 visited)
    (LatticeNearestPlaneThree.threeInto_visited (nearestRefs refs) path.2 visited)

/-- Actual original-sample resident accounting retains every originally supplied runtime entry. -/
theorem pairToNearestPlaneInto_resident_le (refs : Refs ctx N)
    (path : (pairToNearestPlaneInto refs).Path) :
    (pairToNearestPlaneInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [pairToNearestPlaneInto_visited refs path visited present]

/-- Actual original-sample auxiliary accounting retains every original runtime workspace role. -/
theorem pairToNearestPlaneInto_auxiliary_le (refs : Refs ctx N)
    (path : (pairToNearestPlaneInto refs).Path) :
    (pairToNearestPlaneInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [pairToNearestPlaneInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairNearestPlaneMachine
