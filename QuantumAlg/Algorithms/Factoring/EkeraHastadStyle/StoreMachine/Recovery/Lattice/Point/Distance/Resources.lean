/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Distance

/-!
# Actual initialized squared-distance resources
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSquaredDistanceMachine

open Execution

noncomputable section

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Independent three-subtraction and five-instruction self-dot refresh formula. -/
def distanceTrace (width : Nat) : List (Resource.Event model) :=
  LatticePointDifferenceMachine.differenceTrace (model := model) width ++
    [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
      .classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .mulLow width)),
      .classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .add width)),
      .classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .mulLow width)),
      .classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .add width))]

/-- The actual distance path emits exactly the independently specified eight native instructions. -/
lemma squaredDistanceInto_events (refs : Refs ctx width)
    (path : (squaredDistanceInto refs).Path) :
    (squaredDistanceInto refs).eventTrace path = distanceTrace width := by
  change _ ++ _ = _
  rw [LatticePointDifferenceMachine.pointDifferenceInto_events,
    LatticeDotRefresh.refreshInto_events]
  rfl

/-- Actual native multiplicities include explicit initialization and all subsequent arithmetic. -/
lemma squaredDistanceInto_resourcePool (refs : Refs ctx width)
    (path : (squaredDistanceInto refs).Path) :
    (squaredDistanceInto refs).resourcePool path =
      ResourcePool.ofList (distanceTrace width) :=
  congrArg ResourcePool.ofList (squaredDistanceInto_events refs path)

/-- The actual initialized calculation uses exactly eight native instructions. -/
lemma squaredDistanceInto_eventCount (refs : Refs ctx width)
    (path : (squaredDistanceInto refs).Path) :
    ((squaredDistanceInto refs).eventTrace path).length = 8 := rfl

/-- Unit-duration dependency depth charges each of the eight actual arithmetic instructions. -/
lemma squaredDistanceInto_depth (refs : Refs ctx width)
    (path : (squaredDistanceInto refs).Path) :
    (squaredDistanceInto refs).depth (fun _ => 1) path = 8 := rfl

/-- The actual subtraction and self-dot restore the complete borrowed-reference joint state. -/
lemma squaredDistanceInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (squaredDistanceInto refs).BorrowedRestored Reference state
      ((squaredDistanceInto refs).execute environment Reference state) :=
  Circuit.borrowedRestored_seq (environment := environment) _ _ state
    (LatticePointDifferenceMachine.pointDifferenceInto_borrowedRestored refs.difference
      Reference state)
    (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _)

/-- The eight actual instructions retain every original supplied context entry. -/
lemma squaredDistanceInto_visited (refs : Refs ctx width)
    (path : (squaredDistanceInto refs).Path) :
    (squaredDistanceInto refs).visitedContexts path = List.replicate 8 ctx := rfl

/-- Resident accounting retains all original quantum and classical storage during distance work. -/
lemma squaredDistanceInto_resident_le (refs : Refs ctx width)
    (path : (squaredDistanceInto refs).Path) :
    (squaredDistanceInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [squaredDistanceInto_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- Auxiliary accounting uses the original five destinations with no extra allocation. -/
lemma squaredDistanceInto_auxiliary_le (refs : Refs ctx width)
    (path : (squaredDistanceInto refs).Path) :
    (squaredDistanceInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [squaredDistanceInto_visited] at present
  rw [(List.mem_replicate.mp present).2]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSquaredDistanceMachine
