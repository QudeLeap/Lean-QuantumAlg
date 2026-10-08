/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Point.Correctness

/-!
# Actual two-coordinate centered-target resources

Two selected native formulas bound the actual caller-supplied target loader by
fourteen operations. Every original resident cell and borrowed correlation is
retained throughout both chronological coordinate calls.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTargetPoint

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Independent native formula of the two selected centered-coordinate calls. -/
def pointTrace (width : Nat) (firstNegates secondNegates : Bool) : List (Resource.Event model) :=
  LatticeTarget.centeredTrace width firstNegates ++ LatticeTarget.centeredTrace width secondNegates

/-- Every actual two-coordinate path emits the exact independent native formula. -/
theorem loadTargetPointInto_events (refs : Refs ctx width)
    (path : (loadTargetPointInto refs).Path) :
    (loadTargetPointInto refs).eventTrace path = pointTrace width
      (LatticeTarget.selectedNegation refs.first path.1.2)
      (LatticeTarget.selectedNegation refs.second path.2.2) :=
  congrArg₂ List.append (LatticeTarget.centeredTargetInto_events refs.first path.1)
    (LatticeTarget.centeredTargetInto_events refs.second path.2)

/-- Actual two-coordinate multiplicities equal the independently selected native formula. -/
theorem loadTargetPointInto_resourcePool (refs : Refs ctx width)
    (path : (loadTargetPointInto refs).Path) :
    (loadTargetPointInto refs).resourcePool path = ResourcePool.ofList (pointTrace width
      (LatticeTarget.selectedNegation refs.first path.1.2)
      (LatticeTarget.selectedNegation refs.second path.2.2)) :=
  congrArg ResourcePool.ofList (loadTargetPointInto_events refs path)

/-- Placement-independent coordinate envelope of both actual centered calls. -/
def eventEnvelope (width : Nat) : ResourcePool model :=
  LatticeTarget.eventEnvelope width + LatticeTarget.eventEnvelope width

/-- Every actual target-point pool lies in the independent two-coordinate envelope. -/
theorem loadTargetPointInto_resourcePool_le (refs : Refs ctx width)
    (path : (loadTargetPointInto refs).Path) :
    (loadTargetPointInto refs).resourcePool path ≤ eventEnvelope width := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (LatticeTarget.centeredTargetInto_resourcePool_le refs.first path.1)
    (LatticeTarget.centeredTargetInto_resourcePool_le refs.second path.2)

/-- Both actual coordinate calls execute at most fourteen native operations. -/
theorem loadTargetPointInto_eventCount_le (refs : Refs ctx width)
    (path : (loadTargetPointInto refs).Path) :
    ((loadTargetPointInto refs).eventTrace path).length ≤ 14 := by
  have first := LatticeTarget.centeredTargetInto_eventCount_le refs.first path.1
  have second := LatticeTarget.centeredTargetInto_eventCount_le refs.second path.2
  change List.length (_ ++ _) ≤ 14
  rw [List.length_append]
  omega

/-- Chronological unit-duration depth includes both actual comparison and arithmetic calls. -/
theorem loadTargetPointInto_depth_le (refs : Refs ctx width)
    (path : (loadTargetPointInto refs).Path) :
    (loadTargetPointInto refs).depth (fun _ => 1) path ≤ 14 := by
  have first := LatticeTarget.centeredTargetInto_depth_le refs.first path.1
  have second := LatticeTarget.centeredTargetInto_depth_le refs.second path.2
  change (LatticeTarget.centeredTargetInto refs.first).depth (fun _ => 1) path.1 +
    (LatticeTarget.centeredTargetInto refs.second).depth (fun _ => 1) path.2 ≤ 14
  omega

/-- Both actual coordinate calls preserve every original borrowed-reference correlation. -/
theorem loadTargetPointInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (loadTargetPointInto refs).BorrowedRestored Reference state
      ((loadTargetPointInto refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (LatticeTarget.centeredTargetInto_borrowedRestored refs.first Reference state)
    (LatticeTarget.centeredTargetInto_borrowedRestored refs.second Reference _)

/-- Both actual coordinate calls retain exactly the original complete context. -/
theorem loadTargetPointInto_visited (refs : Refs ctx width)
    (path : (loadTargetPointInto refs).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (loadTargetPointInto refs).visitedContexts path) : visited = ctx := by
  change visited ∈ (_ ++ _) at present
  exact (List.mem_append.mp present).elim
    (LatticeTarget.centeredTargetInto_visited refs.first path.1 visited)
    (LatticeTarget.centeredTargetInto_visited refs.second path.2 visited)

/-- All original resident storage remains counted through both actual coordinate calls. -/
theorem loadTargetPointInto_resident_le (refs : Refs ctx width)
    (path : (loadTargetPointInto refs).Path) :
    (loadTargetPointInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [loadTargetPointInto_visited refs path visited present]

/-- All original auxiliary roles remain counted throughout the actual target-point loading. -/
theorem loadTargetPointInto_auxiliary_le (refs : Refs ctx width)
    (path : (loadTargetPointInto refs).Path) :
    (loadTargetPointInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [loadTargetPointInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTargetPoint
