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

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

private lemma firstAdvance_count (refs : Refs ctx width) (path : (firstAdvanceInto (model :=
    model) refs).Path) :
    ((firstAdvanceInto (model := model) refs).eventTrace path).length ≤ 1 := by
  rw [firstAdvanceInto_events]
  unfold firstAdvanceTrace
  split <;> simp [LatticePhaseControl.transitionTrace]

private lemma secondAdvance_count (refs : Refs ctx width) (path : (secondAdvanceInto (model
    := model) refs).Path) :
    ((secondAdvanceInto (model := model) refs).eventTrace path).length = 1 := by
  rw [secondAdvanceInto_events]
  rfl

private lemma firstAdvance_depth (refs : Refs ctx width) (path : (firstAdvanceInto (model :=
    model) refs).Path) :
    (firstAdvanceInto (model := model) refs).depth (fun _ => 1) path ≤ 1 := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag =>
    cases flag
    · change 0 ≤ 1
      decide
    · change 1 ≤ 1
      rfl

private lemma secondAdvance_depth (refs : Refs ctx width) (path : (secondAdvanceInto (model
    := model) refs).Path) :
    (secondAdvanceInto (model := model) refs).depth (fun _ => 1) path = 1 := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag => cases flag <;> rfl

/-- Each actual first driver path uses at most 67 native classical instructions. -/
lemma firstStepInto_eventCount_le (refs : Refs ctx width) (path : (firstStepInto (model :=
    model) refs).Path) :
    ((firstStepInto (model := model) refs).eventTrace path).length ≤ 67 := by
  have pair := LatticeFirstPairMachine.firstPairInto_eventCount_le refs.first path.1
  have advance := firstAdvance_count refs path.2.1
  change List.length (_ ++ (_ ++ _)) ≤ 67
  simp only [List.length_append]
  change ((LatticeFirstPairMachine.firstPairInto (model := model) refs.first).eventTrace
    path.1).length +
    (((firstAdvanceInto (model := model) refs).eventTrace path.2.1).length + 30) ≤ 67
  omega

/-- Actual first-phase unit-duration depth includes the pair, phase update and Gram refresh. -/
lemma firstStepInto_depth_le (refs : Refs ctx width) (path : (firstStepInto (model := model)
    refs).Path) :
    (firstStepInto (model := model) refs).depth (fun _ => 1) path ≤ 67 := by
  have pair := LatticeFirstPairMachine.firstPairInto_depth_le refs.first path.1
  have advance := firstAdvance_depth refs path.2.1
  change (LatticeFirstPairMachine.firstPairInto (model := model) refs.first).depth (fun _ => 1)
    path.1 +
    ((firstAdvanceInto (model := model) refs).depth (fun _ => 1) path.2.1 + 30) ≤ 67
  omega

/-- Each actual second driver path uses at most 130 native classical instructions. -/
lemma secondStepInto_eventCount_le (refs : Refs ctx width) (path : (secondStepInto (model :=
    model) refs).Path) :
    ((secondStepInto (model := model) refs).eventTrace path).length ≤ 130 := by
  have pair := LatticeSecondPairFullMachine.secondPairInto_eventCount_le refs.second path.1
  have advance := secondAdvance_count refs path.2.1
  change List.length (_ ++ (_ ++ _)) ≤ 130
  simp only [List.length_append]
  change ((LatticeSecondPairFullMachine.secondPairInto (model := model) refs.second).eventTrace
    path.1).length +
    (((secondAdvanceInto (model := model) refs).eventTrace path.2.1).length + 30) ≤ 130
  omega

/-- Actual second-phase unit-duration depth includes the pair, phase update and Gram refresh. -/
lemma secondStepInto_depth_le (refs : Refs ctx width) (path : (secondStepInto (model :=
    model) refs).Path) :
    (secondStepInto (model := model) refs).depth (fun _ => 1) path ≤ 130 := by
  have pair := LatticeSecondPairFullMachine.secondPairInto_depth_le refs.second path.1
  have advance := secondAdvance_depth refs path.2.1
  change (LatticeSecondPairFullMachine.secondPairInto (model := model) refs.second).depth (fun
    _ => 1) path.1 +
    ((secondAdvanceInto (model := model) refs).depth (fun _ => 1) path.2.1 + 30) ≤ 130
  omega

/-- Every actual iteration satisfies the independent worst-case eventCount bound 130. -/
lemma stepInto_eventCount_le (refs : Refs ctx width) (path : (stepInto (model := model)
    refs).Path) :
    ((stepInto (model := model) refs).eventTrace path).length ≤ 130 := by
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
lemma stepInto_depth_le (refs : Refs ctx width) (path : (stepInto (model := model) refs).Path) :
    (stepInto (model := model) refs).depth (fun _ => 1) path ≤ 130 := by
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
lemma fixedFuelInto_eventCount_le (fuel : Nat) (refs : Refs ctx width)
    (path : (fixedFuelInto (model := model) fuel refs).Path) :
    ((fixedFuelInto (model := model) fuel refs).eventTrace path).length ≤ 130 * fuel := by
  change (List.ofFn (fun index : Fin fuel =>
    (stepInto (model := model) refs).eventTrace (path index))).flatten.length ≤ _
  simp only [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  calc
    _ ≤ ∑ _index : Fin fuel, 130 := Finset.sum_le_sum
      (fun index _ => stepInto_eventCount_le refs (path index))
    _ = 130 * fuel := by simp [Nat.mul_comm]

/-- Fixed-fuel dependency depth sums the actual serial iteration depths. -/
lemma fixedFuelInto_depth_le (fuel : Nat) (refs : Refs ctx width)
    (path : (fixedFuelInto (model := model) fuel refs).Path) :
    (fixedFuelInto (model := model) fuel refs).depth (fun _ => 1) path ≤ 130 * fuel := by
  change 0 + (∑ index : Fin fuel, (stepInto (model := model) refs).depth (fun _ => 1) (path
    index)) ≤ _
  rw [Nat.zero_add]
  calc
    _ ≤ ∑ _index : Fin fuel, 130 := Finset.sum_le_sum
      (fun index _ => stepInto_depth_le refs (path index))
    _ = 130 * fuel := by simp [Nat.mul_comm]

private lemma firstAdvance_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (firstAdvanceInto (model := model) refs).BorrowedRestored Reference state
      ((firstAdvanceInto (model := model) refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_branch (environment := environment)
    (.storage refs.first.lovasz.passes.toCStorageRef)
    (firstAdvanceArm (model := model) refs) Reference _ state
  intro flag History _ state
  cases flag with
  | bit flag =>
    cases flag
    · exact Circuit.borrowedRestored_id
        (environment := environment) (model := model) (ctx := ctx) state
    · exact LatticePhaseControl.transitionInto_borrowedRestored refs.machine .firstPass
        Reference state

/-- The complete actual first driver restores its full borrowed-reference joint state. -/
lemma firstStepInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (firstStepInto (model := model) refs).BorrowedRestored Reference state
      ((firstStepInto (model := model) refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_seq
    (environment := environment) (LatticeFirstPairMachine.firstPairInto (model := model)
    refs.first)
    (firstTailInto refs)
  · exact LatticeFirstPairMachine.firstPairInto_borrowedRestored refs.first Reference state
  · exact Circuit.borrowedRestored_seq
      (environment := environment) _ _ _ (firstAdvance_borrowedRestored refs Reference _)
      (LatticeMetricMachine.refreshInto_borrowedRestored _ _ Reference _)

private lemma secondAdvance_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (secondAdvanceInto (model := model) refs).BorrowedRestored Reference state
      ((secondAdvanceInto (model := model) refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_branch (environment := environment)
    (.storage refs.second.branch.lovasz.passes.toCStorageRef)
    (secondAdvanceArm (model := model) refs) Reference _ state
  intro flag History _ state
  cases flag with
  | bit flag =>
    cases flag
    · exact LatticePhaseControl.transitionInto_borrowedRestored refs.machine .secondFail
        Reference state
    · exact LatticePhaseControl.transitionInto_borrowedRestored refs.machine .secondPass
        Reference state

/-- The complete actual second driver restores its full borrowed-reference joint state. -/
lemma secondStepInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (secondStepInto (model := model) refs).BorrowedRestored Reference state
      ((secondStepInto (model := model) refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_seq
    (environment := environment) (LatticeSecondPairFullMachine.secondPairInto (model :=
    model) refs.second)
    (secondTailInto refs)
  · exact LatticeSecondPairFullMachine.secondPairInto_borrowedRestored refs.second Reference state
  · exact Circuit.borrowedRestored_seq
      (environment := environment) _ _ _ (secondAdvance_borrowedRestored refs Reference _)
      (LatticeMetricMachine.refreshInto_borrowedRestored _ _ Reference _)

private lemma nonDone_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (nonDoneStepInto (model := model) refs).BorrowedRestored Reference state
      ((nonDoneStepInto (model := model) refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_branch
    (environment := environment) (phaseInput refs.machine.secondPhase)
    (nonDoneArm (model := model) refs) Reference _ state
  intro flag History _ state
  cases flag with
  | bit flag =>
    cases flag
    · exact firstStepInto_borrowedRestored refs Reference state
    · exact secondStepInto_borrowedRestored refs Reference state

/-- Terminal identity and every actual nonterminal branch restore all borrowed correlations. -/
lemma stepInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (stepInto (model := model) refs).BorrowedRestored Reference state
      ((stepInto (model := model) refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_branch (environment := environment) (phaseInput refs.machine.done)
    (stepArm (model := model) refs) Reference _ state
  intro flag History _ state
  cases flag with
  | bit flag =>
    cases flag
    · exact nonDone_borrowedRestored refs Reference state
    · exact Circuit.borrowedRestored_id
        (environment := environment) (model := model) (ctx := ctx) state

/-- Every finite actual driver run restores the complete borrowed-reference joint state. -/
lemma fixedFuelInto_borrowedRestored (fuel : Nat) (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (fixedFuelInto (model := model) fuel refs).BorrowedRestored Reference state
      ((fixedFuelInto (model := model) fuel refs).execute environment Reference state) :=
  Circuit.borrowedRestored_iterate
    (environment := environment) (stepInto (model := model) refs) Reference
    (stepInto_borrowedRestored refs Reference) fuel state

private lemma firstAdvance_visited (refs : Refs ctx width)
    (path : (firstAdvanceInto (model := model) refs).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (firstAdvanceInto (model := model) refs).visitedContexts path) :
      visited = ctx := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag =>
    cases flag
    · exact List.mem_singleton.mp present
    · exact List.mem_singleton.mp present

/-- Every actual first driver instruction uses the complete supplied context. -/
lemma firstStepInto_visited (refs : Refs ctx width) (path : (firstStepInto (model := model)
    refs).Path)
    (visited : RuntimeCtx model.kind) (present : visited ∈ (firstStepInto (model := model)
      refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (_ ++ (_ ++ _)) at present
  simp only [List.mem_append] at present
  rcases present with pair | advance | gram
  · exact LatticeFirstPairMachine.firstPairInto_visited refs.first path.1 visited pair
  · exact firstAdvance_visited refs path.2.1 visited advance
  · rw [LatticeMetricMachine.refreshInto_visited] at gram
    exact (List.mem_replicate.mp gram).2

private lemma secondAdvance_visited (refs : Refs ctx width)
    (path : (secondAdvanceInto (model := model) refs).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (secondAdvanceInto (model := model) refs).visitedContexts path) :
      visited = ctx := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag =>
    cases flag
    · exact List.mem_singleton.mp present
    · exact List.mem_singleton.mp present

/-- Every actual second driver instruction uses the complete supplied context. -/
lemma secondStepInto_visited (refs : Refs ctx width) (path : (secondStepInto (model := model)
    refs).Path)
    (visited : RuntimeCtx model.kind) (present : visited ∈ (secondStepInto (model := model)
      refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (_ ++ (_ ++ _)) at present
  simp only [List.mem_append] at present
  rcases present with pair | advance | gram
  · exact LatticeSecondPairFullMachine.secondPairInto_visited refs.second path.1 visited pair
  · exact secondAdvance_visited refs path.2.1 visited advance
  · rw [LatticeMetricMachine.refreshInto_visited] at gram
    exact (List.mem_replicate.mp gram).2

/-- Terminal identity and every actual selected pair use only the original complete context. -/
lemma stepInto_visited (refs : Refs ctx width) (path : (stepInto (model := model) refs).Path)
    (visited : RuntimeCtx model.kind) (present : visited ∈ (stepInto (model := model)
      refs).visitedContexts path) :
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
lemma fixedFuelInto_visited (fuel : Nat) (refs : Refs ctx width)
    (path : (fixedFuelInto (model := model) fuel refs).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (fixedFuelInto (model := model) fuel refs).visitedContexts path) :
      visited = ctx := by
  change visited ∈ ctx :: (List.ofFn (fun index : Fin fuel =>
    (stepInto (model := model) refs).visitedContexts (path index))).flatten at present
  rcases List.mem_cons.mp present with same | later
  · exact same
  · rcases List.mem_flatten.mp later with ⟨contexts, member, present⟩
    rcases List.mem_ofFn.mp member with ⟨index, rfl⟩
    exact stepInto_visited refs (path index) visited present

/-- Every actual resident peak counts the complete supplied context throughout execution. -/
lemma stepInto_resident_le (refs : Refs ctx width)
    (path : (stepInto (model := model) refs).Path) :
    (stepInto (model := model) refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [stepInto_visited refs path visited present]

/-- Every actual auxiliary peak counts the complete supplied context throughout execution. -/
lemma stepInto_auxiliary_le (refs : Refs ctx width)
    (path : (stepInto (model := model) refs).Path) :
    (stepInto (model := model) refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [stepInto_visited refs path visited present]

/-- Every actual resident peak counts the complete supplied context throughout execution. -/
lemma fixedFuelInto_resident_le (fuel : Nat) (refs : Refs ctx width)
    (path : (fixedFuelInto (model := model) fuel refs).Path) :
    (fixedFuelInto (model := model) fuel refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [fixedFuelInto_visited fuel refs path visited present]

/-- Every actual auxiliary peak counts the complete supplied context throughout execution. -/
lemma fixedFuelInto_auxiliary_le (fuel : Nat) (refs : Refs ctx width)
    (path : (fixedFuelInto (model := model) fuel refs).Path) :
    (fixedFuelInto (model := model) fuel refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [fixedFuelInto_visited fuel refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine
