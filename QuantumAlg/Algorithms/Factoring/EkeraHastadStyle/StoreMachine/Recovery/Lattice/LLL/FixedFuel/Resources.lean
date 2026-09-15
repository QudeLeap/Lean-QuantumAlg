/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Events
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Actual fixed-fuel LLL resource bounds and restoration

One first-phase iteration uses at most 67 operations; one second-phase
iteration uses at most 130. The same bounds hold for unit-duration dependency
depth. Every actual finite run keeps the supplied live context and restores
its borrowed interface jointly with all external reference systems.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem firstAdvance_count (refs : Refs ctx width) (path : (firstAdvanceInto refs).Path) :
    ((firstAdvanceInto refs).eventTrace path).length ≤ 1 := by
  rw [firstAdvanceInto_events]
  unfold firstAdvanceTrace
  split <;> simp

private theorem secondAdvance_count (refs : Refs ctx width) (path : (secondAdvanceInto refs).Path) :
    ((secondAdvanceInto refs).eventTrace path).length = 1 := by
  rw [secondAdvanceInto_events]
  rfl

private theorem firstAdvance_depth (refs : Refs ctx width) (path : (firstAdvanceInto refs).Path) :
    (firstAdvanceInto refs).depth (fun _ => 1) path ≤ 1 := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag =>
    cases flag
    · change 0 ≤ 1
      decide
    · change 1 ≤ 1
      rfl

private theorem secondAdvance_depth (refs : Refs ctx width) (path : (secondAdvanceInto refs).Path) :
    (secondAdvanceInto refs).depth (fun _ => 1) path = 1 := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag => cases flag <;> rfl

/-- Each actual first driver path uses at most 67 native classical instructions. -/
theorem firstStepInto_eventCount_le (refs : Refs ctx width) (path : (firstStepInto refs).Path) :
    ((firstStepInto refs).eventTrace path).length ≤ 67 := by
  have pair := LatticeFirstPairMachine.firstPairInto_eventCount_le refs.first path.1
  have advance := firstAdvance_count refs path.2.1
  change List.length (_ ++ (_ ++ _)) ≤ 67
  simp only [List.length_append]
  change ((LatticeFirstPairMachine.firstPairInto refs.first).eventTrace path.1).length +
    (((firstAdvanceInto refs).eventTrace path.2.1).length + 30) ≤ 67
  omega

/-- Actual first-phase unit-duration depth includes the pair, phase update and Gram refresh. -/
theorem firstStepInto_depth_le (refs : Refs ctx width) (path : (firstStepInto refs).Path) :
    (firstStepInto refs).depth (fun _ => 1) path ≤ 67 := by
  have pair := LatticeFirstPairMachine.firstPairInto_depth_le refs.first path.1
  have advance := firstAdvance_depth refs path.2.1
  change (LatticeFirstPairMachine.firstPairInto refs.first).depth (fun _ => 1) path.1 +
    ((firstAdvanceInto refs).depth (fun _ => 1) path.2.1 + 30) ≤ 67
  omega

/-- Each actual second driver path uses at most 130 native classical instructions. -/
theorem secondStepInto_eventCount_le (refs : Refs ctx width) (path : (secondStepInto refs).Path) :
    ((secondStepInto refs).eventTrace path).length ≤ 130 := by
  have pair := LatticeSecondPairFullMachine.secondPairInto_eventCount_le refs.second path.1
  have advance := secondAdvance_count refs path.2.1
  change List.length (_ ++ (_ ++ _)) ≤ 130
  simp only [List.length_append]
  change ((LatticeSecondPairFullMachine.secondPairInto refs.second).eventTrace path.1).length +
    (((secondAdvanceInto refs).eventTrace path.2.1).length + 30) ≤ 130
  omega

/-- Actual second-phase unit-duration depth includes the pair, phase update and Gram refresh. -/
theorem secondStepInto_depth_le (refs : Refs ctx width) (path : (secondStepInto refs).Path) :
    (secondStepInto refs).depth (fun _ => 1) path ≤ 130 := by
  have pair := LatticeSecondPairFullMachine.secondPairInto_depth_le refs.second path.1
  have advance := secondAdvance_depth refs path.2.1
  change (LatticeSecondPairFullMachine.secondPairInto refs.second).depth (fun _ => 1) path.1 +
    ((secondAdvanceInto refs).depth (fun _ => 1) path.2.1 + 30) ≤ 130
  omega

/-- Every actual iteration satisfies the independent worst-case eventCount bound 130. -/
theorem stepInto_eventCount_le (refs : Refs ctx width) (path : (stepInto refs).Path) :
    ((stepInto refs).eventTrace path).length ≤ 130 := by
  rcases path with ⟨done, path⟩
  cases done with
  | bit done =>
    cases done
    · rcases path with ⟨second, path⟩
      cases second with
      | bit second =>
        cases second
        · exact (firstStepInto_eventCount_le refs path).trans (by decide)
        · exact secondStepInto_eventCount_le refs path
    · change 0 ≤ 130
      decide

/-- Every actual iteration satisfies the independent worst-case depth bound 130. -/
theorem stepInto_depth_le (refs : Refs ctx width) (path : (stepInto refs).Path) :
    (stepInto refs).depth (fun _ => 1) path ≤ 130 := by
  rcases path with ⟨done, path⟩
  cases done with
  | bit done =>
    cases done
    · rcases path with ⟨second, path⟩
      cases second with
      | bit second =>
        cases second
        · exact (firstStepInto_depth_le refs path).trans (by decide)
        · exact secondStepInto_depth_le refs path
    · change 0 ≤ 130
      decide

/-- A fixed number of actual iterations uses at most 130 times that many native operations. -/
theorem fixedFuelInto_eventCount_le (fuel : Nat) (refs : Refs ctx width)
    (path : (fixedFuelInto fuel refs).Path) :
    ((fixedFuelInto fuel refs).eventTrace path).length ≤ 130 * fuel := by
  change (List.ofFn (fun index : Fin fuel =>
    (stepInto refs).eventTrace (path index))).flatten.length ≤ _
  simp only [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  calc
    _ ≤ ∑ _index : Fin fuel, 130 := Finset.sum_le_sum
      (fun index _ => stepInto_eventCount_le refs (path index))
    _ = 130 * fuel := by simp [Nat.mul_comm]

/-- Fixed-fuel dependency depth sums the actual serial iteration depths. -/
theorem fixedFuelInto_depth_le (fuel : Nat) (refs : Refs ctx width)
    (path : (fixedFuelInto fuel refs).Path) :
    (fixedFuelInto fuel refs).depth (fun _ => 1) path ≤ 130 * fuel := by
  change 0 + (∑ index : Fin fuel, (stepInto refs).depth (fun _ => 1) (path index)) ≤ _
  rw [Nat.zero_add]
  calc
    _ ≤ ∑ _index : Fin fuel, 130 := Finset.sum_le_sum
      (fun index _ => stepInto_depth_le refs (path index))
    _ = 130 * fuel := by simp [Nat.mul_comm]

private theorem firstAdvance_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (firstAdvanceInto refs).BorrowedRestored Reference state
      ((firstAdvanceInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_branch _ _ Reference _ state
  intro flag History _ state
  cases flag with
  | bit flag =>
    cases flag
    · change (Circuit.id ctx).BorrowedRestored Reference state
        ((Circuit.id ctx).execute Reference state)
      rw [Circuit.BorrowedRestored, observeBorrowedAfter_sameContext, Circuit.execute_id]
      exact observeBorrowed_mapHistory state _
    · exact LatticePhaseControl.transitionInto_borrowedRestored refs.machine .firstPass
        Reference state

/-- The complete actual first driver restores its full borrowed-reference joint state. -/
theorem firstStepInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (firstStepInto refs).BorrowedRestored Reference state
      ((firstStepInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq (LatticeFirstPairMachine.firstPairInto refs.first)
    (firstTailInto refs)
  · exact LatticeFirstPairMachine.firstPairInto_borrowedRestored refs.first Reference state
  · exact Circuit.borrowedRestored_seq _ _ _ (firstAdvance_borrowedRestored refs Reference _)
      (LatticeMetricMachine.refreshInto_borrowedRestored _ _ Reference _)

private theorem secondAdvance_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (secondAdvanceInto refs).BorrowedRestored Reference state
      ((secondAdvanceInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_branch _ _ Reference _ state
  intro flag History _ state
  cases flag with
  | bit flag =>
    cases flag
    · exact LatticePhaseControl.transitionInto_borrowedRestored refs.machine .secondFail
        Reference state
    · exact LatticePhaseControl.transitionInto_borrowedRestored refs.machine .secondPass
        Reference state

/-- The complete actual second driver restores its full borrowed-reference joint state. -/
theorem secondStepInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (secondStepInto refs).BorrowedRestored Reference state
      ((secondStepInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq (LatticeSecondPairFullMachine.secondPairInto refs.second)
    (secondTailInto refs)
  · exact LatticeSecondPairFullMachine.secondPairInto_borrowedRestored refs.second Reference state
  · exact Circuit.borrowedRestored_seq _ _ _ (secondAdvance_borrowedRestored refs Reference _)
      (LatticeMetricMachine.refreshInto_borrowedRestored _ _ Reference _)

private theorem nonDone_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (nonDoneStepInto refs).BorrowedRestored Reference state
      ((nonDoneStepInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_branch _ _ Reference _ state
  intro flag History _ state
  cases flag with
  | bit flag =>
    cases flag
    · exact firstStepInto_borrowedRestored refs Reference state
    · exact secondStepInto_borrowedRestored refs Reference state

/-- Terminal identity and every actual nonterminal branch restore all borrowed correlations. -/
theorem stepInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (stepInto refs).BorrowedRestored Reference state
      ((stepInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_branch _ _ Reference _ state
  intro flag History _ state
  cases flag with
  | bit flag =>
    cases flag
    · exact nonDone_borrowedRestored refs Reference state
    · change (Circuit.id ctx).BorrowedRestored Reference state
        ((Circuit.id ctx).execute Reference state)
      rw [Circuit.BorrowedRestored, observeBorrowedAfter_sameContext, Circuit.execute_id]
      exact observeBorrowed_mapHistory state _

/-- Every finite actual driver run restores the complete borrowed-reference joint state. -/
theorem fixedFuelInto_borrowedRestored (fuel : Nat) (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (fixedFuelInto fuel refs).BorrowedRestored Reference state
      ((fixedFuelInto fuel refs).execute Reference state) :=
  Circuit.borrowedRestored_iterate (stepInto refs) Reference
    (stepInto_borrowedRestored refs Reference) fuel state

private theorem firstAdvance_visited (refs : Refs ctx width)
    (path : (firstAdvanceInto refs).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (firstAdvanceInto refs).visitedContexts path) : visited = ctx := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag =>
    cases flag
    · exact List.mem_singleton.mp present
    · exact List.mem_singleton.mp present

/-- Every actual first driver instruction uses the complete supplied context. -/
theorem firstStepInto_visited (refs : Refs ctx width) (path : (firstStepInto refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (firstStepInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (_ ++ (_ ++ _)) at present
  simp only [List.mem_append] at present
  rcases present with pair | advance | gram
  · exact LatticeFirstPairMachine.firstPairInto_visited refs.first path.1 visited pair
  · exact firstAdvance_visited refs path.2.1 visited advance
  · rw [LatticeMetricMachine.refreshInto_visited] at gram
    exact (List.mem_replicate.mp gram).2

private theorem secondAdvance_visited (refs : Refs ctx width)
    (path : (secondAdvanceInto refs).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (secondAdvanceInto refs).visitedContexts path) : visited = ctx := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag =>
    cases flag
    · exact List.mem_singleton.mp present
    · exact List.mem_singleton.mp present

/-- Every actual second driver instruction uses the complete supplied context. -/
theorem secondStepInto_visited (refs : Refs ctx width) (path : (secondStepInto refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (secondStepInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (_ ++ (_ ++ _)) at present
  simp only [List.mem_append] at present
  rcases present with pair | advance | gram
  · exact LatticeSecondPairFullMachine.secondPairInto_visited refs.second path.1 visited pair
  · exact secondAdvance_visited refs path.2.1 visited advance
  · rw [LatticeMetricMachine.refreshInto_visited] at gram
    exact (List.mem_replicate.mp gram).2

/-- Terminal identity and every actual selected pair use only the original complete context. -/
theorem stepInto_visited (refs : Refs ctx width) (path : (stepInto refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (stepInto refs).visitedContexts path) :
    visited = ctx := by
  rcases path with ⟨done, path⟩
  cases done with
  | bit done =>
    cases done
    · rcases path with ⟨second, path⟩
      cases second with
      | bit second =>
        cases second
        · exact firstStepInto_visited refs path visited present
        · exact secondStepInto_visited refs path visited present
    · exact List.mem_singleton.mp present

/-- Every actual finite run visits only its complete original supplied live context. -/
theorem fixedFuelInto_visited (fuel : Nat) (refs : Refs ctx width)
    (path : (fixedFuelInto fuel refs).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (fixedFuelInto fuel refs).visitedContexts path) : visited = ctx := by
  change visited ∈ ctx :: (List.ofFn (fun index : Fin fuel =>
    (stepInto refs).visitedContexts (path index))).flatten at present
  rcases List.mem_cons.mp present with same | later
  · exact same
  · rcases List.mem_flatten.mp later with ⟨contexts, member, present⟩
    rcases List.mem_ofFn.mp member with ⟨index, rfl⟩
    exact stepInto_visited refs (path index) visited present

/-- Every actual resident peak counts the complete supplied context throughout execution. -/
theorem stepInto_resident_le (refs : Refs ctx width)
    (path : (stepInto refs).Path) :
    (stepInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [stepInto_visited refs path visited present]

/-- Every actual auxiliary peak counts the complete supplied context throughout execution. -/
theorem stepInto_auxiliary_le (refs : Refs ctx width)
    (path : (stepInto refs).Path) :
    (stepInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [stepInto_visited refs path visited present]

/-- Every actual resident peak counts the complete supplied context throughout execution. -/
theorem fixedFuelInto_resident_le (fuel : Nat) (refs : Refs ctx width)
    (path : (fixedFuelInto fuel refs).Path) :
    (fixedFuelInto fuel refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [fixedFuelInto_visited fuel refs path visited present]

/-- Every actual auxiliary peak counts the complete supplied context throughout execution. -/
theorem fixedFuelInto_auxiliary_le (fuel : Nat) (refs : Refs ctx width)
    (path : (fixedFuelInto fuel refs).Path) :
    (fixedFuelInto fuel refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [fixedFuelInto_visited fuel refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine
