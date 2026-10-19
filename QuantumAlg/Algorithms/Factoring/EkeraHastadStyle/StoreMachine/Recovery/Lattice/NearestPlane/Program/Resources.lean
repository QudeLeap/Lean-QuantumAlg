/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Third.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Second.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.First.Resources

/-!
# Actual three-stage nearest-plane resources

The independent chronological instruction formula combines the three native
phase formulas. Every path uses at most 128 native operations and retains all
original resources, including the full borrowed-reference joint state.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThree

open Execution

noncomputable section

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Independent native instruction formula for the eleven recorded sign decisions. -/
def phaseTrace (width : Nat) (denominatorNegative numeratorNegative : Bool)
    (thirdMagnitude thirdCorrection thirdRestore : Bool)
    (secondMagnitude secondCorrection secondRestore : Bool)
    (firstMagnitude firstCorrection firstRestore : Bool) : List (Resource.Event model) :=
  LatticeNearestPlaneThird.phaseTrace width denominatorNegative numeratorNegative
    thirdMagnitude thirdCorrection thirdRestore ++
      (LatticeNearestPlaneSecond.phaseTrace width secondMagnitude secondCorrection secondRestore ++
        LatticeNearestPlaneFirst.phaseTrace width firstMagnitude firstCorrection firstRestore)

/-- The chronological actual path has exactly the independent native instruction trace. -/
lemma threeInto_events (refs : Refs ctx width) (path : (threeInto refs).Path) :
    (threeInto refs).eventTrace path =
      let thirdSuffix := path.1.2
      let thirdDivision := thirdSuffix.2.2.1
      let secondDivision := path.2.1.2.2.1
      let firstDivision := path.2.2.2.2.1
      phaseTrace width thirdSuffix.1.2.1.toBool thirdSuffix.2.1.1.toBool
        thirdDivision.1.1.2.1.toBool thirdDivision.2.1.2.1.1.toBool
        thirdDivision.2.2.2.2.1.toBool secondDivision.1.1.2.1.toBool
        secondDivision.2.1.2.1.1.toBool secondDivision.2.2.2.2.1.toBool
        firstDivision.1.1.2.1.toBool firstDivision.2.1.2.1.1.toBool
        firstDivision.2.2.2.2.1.toBool := by
  change _ ++ (_ ++ _) = _
  rw [LatticeNearestPlaneThird.thirdInto_events, LatticeNearestPlaneSecond.secondInto_events,
    LatticeNearestPlaneFirst.firstInto_events]
  rfl

/-- Native multiplicities are counted from the same independently specified instructions. -/
lemma threeInto_resourcePool (refs : Refs ctx width) (path : (threeInto refs).Path) :
    (threeInto refs).resourcePool path =
      let thirdSuffix := path.1.2
      let thirdDivision := thirdSuffix.2.2.1
      let secondDivision := path.2.1.2.2.1
      let firstDivision := path.2.2.2.2.1
      ResourcePool.ofList (phaseTrace width thirdSuffix.1.2.1.toBool thirdSuffix.2.1.1.toBool
        thirdDivision.1.1.2.1.toBool thirdDivision.2.1.2.1.1.toBool
        thirdDivision.2.2.2.2.1.toBool secondDivision.1.1.2.1.toBool
        secondDivision.2.1.2.1.1.toBool secondDivision.2.2.2.2.1.toBool
        firstDivision.1.1.2.1.toBool firstDivision.2.1.2.1.1.toBool
        firstDivision.2.2.2.2.1.toBool) := by
  change ResourcePool.ofList ((threeInto refs).eventTrace path) = _
  rw [threeInto_events]

/-- At most 128 native instructions execute across all three actual coordinate reductions. -/
lemma threeInto_eventCount_le (refs : Refs ctx width) (path : (threeInto refs).Path) :
    ((threeInto refs).eventTrace path).length ≤ 128 := by
  have third := LatticeNearestPlaneThird.thirdInto_eventCount_le (thirdRefs refs) path.1
  have second := LatticeNearestPlaneSecond.secondInto_eventCount_le (secondRefs refs) path.2.1
  have first := LatticeNearestPlaneFirst.firstInto_eventCount_le (firstRefs refs) path.2.2
  change List.length (_ ++ (_ ++ _)) ≤ 128
  simp only [List.length_append]
  omega

/-- Serial depth includes the dependence of each reduction on its predecessor's actual residual. -/
lemma threeInto_depth_le (refs : Refs ctx width) (path : (threeInto refs).Path) :
    (threeInto refs).depth (fun _ => 1) path ≤ 128 := by
  have third := LatticeNearestPlaneThird.thirdInto_depth_le (thirdRefs refs) path.1
  have second := LatticeNearestPlaneSecond.secondInto_depth_le (secondRefs refs) path.2.1
  have first := LatticeNearestPlaneFirst.firstInto_depth_le (firstRefs refs) path.2.2
  change (LatticeNearestPlaneThird.thirdInto (thirdRefs refs)).depth (fun _ => 1) path.1 +
    ((LatticeNearestPlaneSecond.secondInto (secondRefs refs)).depth (fun _ => 1) path.2.1 +
      (LatticeNearestPlaneFirst.firstInto (firstRefs refs)).depth (fun _ => 1) path.2.2) ≤ 128
  omega

/-- Complete execution restores borrowed state jointly with every external quantum reference. -/
lemma threeInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (threeInto refs).BorrowedRestored Reference state
      ((threeInto refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_seq (environment := environment)
  · exact LatticeNearestPlaneThird.thirdInto_borrowedRestored _ Reference state
  · exact Circuit.borrowedRestored_seq (environment := environment) _ _ _
      (LatticeNearestPlaneSecond.secondInto_borrowedRestored _ Reference _)
      (LatticeNearestPlaneFirst.firstInto_borrowedRestored _ Reference _)

/-- All three actual reductions use exactly the supplied context without hidden allocation. -/
lemma threeInto_visited (refs : Refs ctx width) (path : (threeInto refs).Path)
    (visited : RuntimeCtx model.kind) (present : visited ∈ (threeInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (_ ++ (_ ++ _)) at present
  simp only [List.mem_append] at present
  rcases present with third | second | first
  · exact LatticeNearestPlaneThird.thirdInto_visited (thirdRefs refs) path.1 visited third
  · exact LatticeNearestPlaneSecond.secondInto_visited (secondRefs refs) path.2.1 visited second
  · exact LatticeNearestPlaneFirst.firstInto_visited (firstRefs refs) path.2.2 visited first

/-- Resident space includes every supplied quantum dimension and actual classical cell. -/
lemma threeInto_resident_le (refs : Refs ctx width) (path : (threeInto refs).Path) :
    (threeInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [threeInto_visited refs path visited present]

/-- Auxiliary space retains all original roles throughout the actual three-stage execution. -/
lemma threeInto_auxiliary_le (refs : Refs ctx width) (path : (threeInto refs).Path) :
    (threeInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [threeInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThree
