/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Program

/-!
# Complete actual second-pair resources

Independent native instruction formulas compose using the six actual rounded-
division sign decisions and the actual final Lovasz bit. The complete transition
has at most 99 operations and unit-duration depth, keeps the original live
context, and restores the borrowed interface jointly with external references.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairFullMachine

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent chronological formula for the six quotient signs and final Lovasz decision. -/
def secondPairTrace (width : Nat)
    (firstMagnitude firstCorrection firstRestore secondMagnitude secondCorrection
      secondRestore passes : Bool) : List (Resource.Event kind) :=
  (LatticeSecondPairMachine.secondPairPrefixTrace width firstMagnitude firstCorrection
    firstRestore ++
    LatticeSecondPairPostReduction.postReductionTrace width secondMagnitude secondCorrection
      secondRestore) ++
    (LatticeAreaRefresh.phaseTrace width ++
      (LatticeAreaRefresh.phaseTrace width ++ LatticeSecondLovaszBranch.branchTrace width passes))

/-- Every actual full path emits exactly the independent formula at its own recorded decisions. -/
theorem secondPairInto_events (refs : Refs ctx width) (path : (secondPairInto refs).Path) :
    (secondPairInto refs).eventTrace path = secondPairTrace width
      path.1.1.2.1.1.1.2.1.toBool path.1.1.2.1.2.1.2.1.1.toBool
      path.1.1.2.1.2.2.2.2.1.toBool path.1.2.2.1.1.1.2.1.toBool
      path.1.2.2.1.2.1.2.1.1.toBool path.1.2.2.1.2.2.2.2.1.toBool path.2.2.2.2.1.toBool := by
  change (_ ++ _) ++ (_ ++ (_ ++ _)) = _
  rw [LatticeSecondPairMachine.secondPairPrefixInto_events,
    LatticeSecondPairPostReduction.postReductionInto_events, LatticeAreaRefresh.refreshInto_events,
    LatticeAreaRefresh.refreshInto_events, LatticeSecondLovaszBranch.branchInto_events]
  rfl

/-- The complete native resource pool equals the independent formula at the actual decisions. -/
theorem secondPairInto_resourcePool (refs : Refs ctx width) (path : (secondPairInto refs).Path) :
    (secondPairInto refs).resourcePool path = ResourcePool.ofList (secondPairTrace width
      path.1.1.2.1.1.1.2.1.toBool path.1.1.2.1.2.1.2.1.1.toBool
      path.1.1.2.1.2.2.2.2.1.toBool path.1.2.2.1.1.1.2.1.toBool
      path.1.2.2.1.2.1.2.1.1.toBool path.1.2.2.1.2.2.2.2.1.toBool path.2.2.2.2.1.toBool) := by
  change ResourcePool.ofList ((secondPairInto refs).eventTrace path) = _
  rw [secondPairInto_events]

/-- Every actual complete second-pair path executes at most 99 native classical operations. -/
theorem secondPairInto_eventCount_le (refs : Refs ctx width) (path : (secondPairInto refs).Path) :
    ((secondPairInto refs).eventTrace path).length ≤ 99 := by
  have first := LatticeSecondPairMachine.secondPairPrefixInto_eventCount_le refs.machine path.1.1
  have second := LatticeSecondPairPostReduction.postReductionInto_eventCount_le refs.post path.1.2
  have branch := LatticeSecondLovaszBranch.branchInto_eventCount_le refs.branch path.2.2.2
  change List.length ((_ ++ _) ++ (_ ++ (_ ++ _))) ≤ 99
  simp only [List.length_append]
  change (((LatticeSecondPairMachine.secondPairPrefixInto refs.machine).eventTrace
    path.1.1).length +
    ((LatticeSecondPairPostReduction.postReductionInto refs.post).eventTrace path.1.2).length) +
      (14 + (14 + ((LatticeSecondLovaszBranch.branchInto refs.branch).eventTrace
        path.2.2.2).length)) ≤ 99
  omega

/-- Unit-duration serial depth includes the dependencies between all five actual phases. -/
theorem secondPairInto_depth_le (refs : Refs ctx width) (path : (secondPairInto refs).Path) :
    (secondPairInto refs).depth (fun _ => 1) path ≤ 99 := by
  have first := LatticeSecondPairMachine.secondPairPrefixInto_depth_le refs.machine path.1.1
  have second := LatticeSecondPairPostReduction.postReductionInto_depth_le refs.post path.1.2
  have branch := LatticeSecondLovaszBranch.branchInto_depth_le refs.branch path.2.2.2
  change ((LatticeSecondPairMachine.secondPairPrefixInto refs.machine).depth (fun _ => 1) path.1.1 +
    (LatticeSecondPairPostReduction.postReductionInto refs.post).depth (fun _ => 1) path.1.2) +
      (14 + (14 + (LatticeSecondLovaszBranch.branchInto refs.branch).depth (fun _ => 1)
        path.2.2.2)) ≤ 99
  omega

/-- Actual complete execution restores borrowed correlations jointly with every reference. -/
theorem secondPairInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (secondPairInto refs).BorrowedRestored Reference state
      ((secondPairInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq (sizeReductionInto refs) (areaBranchInto refs)
  · exact Circuit.borrowedRestored_seq _ _ state
      (LatticeSecondPairMachine.secondPairPrefixInto_borrowedRestored refs.machine Reference state)
      (LatticeSecondPairPostReduction.postReductionInto_borrowedRestored refs.post Reference _)
  · apply Circuit.borrowedRestored_seq
      (LatticeAreaRefresh.refreshInto refs.machine.basis.first refs.machine.basis.second
        refs.area12)
      (area13BranchInto refs)
    · exact LatticeAreaRefresh.refreshInto_borrowedRestored _ _ _ Reference _
    · exact Circuit.borrowedRestored_seq _ _ _
        (LatticeAreaRefresh.refreshInto_borrowedRestored _ _ _ Reference _)
        (LatticeSecondLovaszBranch.branchInto_borrowedRestored refs.branch Reference _)

/-- Every phase and actual selected arm uses the complete supplied context. -/
theorem secondPairInto_visited (refs : Refs ctx width) (path : (secondPairInto refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (secondPairInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ ((_ ++ _) ++ (_ ++ (_ ++ _))) at present
  simp only [List.mem_append] at present
  rcases present with (first | second) | area12 | area13 | branch
  · exact LatticeSecondPairMachine.secondPairPrefixInto_visited refs.machine path.1.1 visited first
  · exact LatticeSecondPairPostReduction.postReductionInto_visited refs.post path.1.2 visited second
  · exact LatticeAreaRefresh.refreshInto_visited _ _ _ path.2.1 visited area12
  · exact LatticeAreaRefresh.refreshInto_visited _ _ _ path.2.2.1 visited area13
  · exact LatticeSecondLovaszBranch.branchInto_visited refs.branch path.2.2.2 visited branch

/-- Resident accounting includes all supplied quantum dimensions and actual classical cells. -/
theorem secondPairInto_resident_le (refs : Refs ctx width) (path : (secondPairInto refs).Path) :
    (secondPairInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [secondPairInto_visited refs path visited present]

/-- Auxiliary accounting retains the supplied roles throughout every actual phase. -/
theorem secondPairInto_auxiliary_le (refs : Refs ctx width) (path : (secondPairInto refs).Path) :
    (secondPairInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [secondPairInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairFullMachine
