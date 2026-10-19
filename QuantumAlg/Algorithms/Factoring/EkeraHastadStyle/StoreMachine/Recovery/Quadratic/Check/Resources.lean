/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Check.Program
import all QuantumAlg.Components.Classical.NumberTheory.Nat.ModCheck.Resources

/-!
# Independent native quadratic-check resources and joint borrowed restoration

The positive suffix has five native operations. The complete checker adds its
actual lower-bound comparison and executes either that suffix or one charged
clear. Its original maximum branch allowance is independent of the run.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidateCheck

open Execution
open ClassicalRoutines.NumberTheory

noncomputable section

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {shortWidth : Nat}

/-- Original independent positive-candidate native coordinate allowance. -/
def positiveEventEnvelope (shortWidth : Nat) : ResourcePool model :=
  ResourcePool.singleton (.classicalOperation
      (BitWord.selectedCoordinate (execution := model)
        (.wordResize (CandidateWidth shortWidth) (ModulusWidth shortWidth)))) +
    (ResourcePool.singleton
        (.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .lessThan (ModulusWidth shortWidth)))) +
      (NatModCheck.eventEnvelope (ModulusWidth shortWidth) (CandidateWidth shortWidth) +
        ResourcePool.singleton (.classicalOperation
          (BitWord.selectedCoordinate (execution := model) (.bit .and)))))

/-- Original independent decision plus maximum selected-branch coordinate allowance. -/
def eventEnvelope (shortWidth : Nat) : ResourcePool model :=
  ResourcePool.singleton
      (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .lessThan (CandidateWidth shortWidth)))) +
    ResourcePool.max (positiveEventEnvelope shortWidth)
      (ResourcePool.singleton (.classicalOperation
        (BitWord.selectedCoordinate (execution := model) (.bit .xor))))

/-- The original five chronological positive-candidate native operations. -/
def positiveTrace (shortWidth : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize (CandidateWidth shortWidth) (ModulusWidth shortWidth))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .lessThan (ModulusWidth shortWidth))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.divRem (ModulusWidth shortWidth) (CandidateWidth shortWidth))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .equal (CandidateWidth shortWidth))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .and))]

/-- Independent chronological formula selected by the actual recorded lower-bound flag. -/
def nativeTrace (shortWidth : Nat) (selected : Bool) : List (Resource.Event model) :=
  .classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordBinary .lessThan (CandidateWidth shortWidth))) ::
    if selected then positiveTrace shortWidth else
      [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .xor))]

/-- The actual positive suffix has exactly the original five-instruction trace. -/
lemma positiveInto_events (refs : Refs ctx shortWidth) (path : (positiveInto refs).Path) :
    (positiveInto refs).eventTrace path = positiveTrace shortWidth := by
  change (BitWord.instruction (execution := model) (widenOp refs)).eventTrace path.1 ++
    ((BitWord.instruction (execution := model) (belowOp refs)).eventTrace path.2.1 ++
      ((NatModCheck.into refs.modulusCheck).eventTrace path.2.2.1 ++
        (BitWord.instruction (execution := model) (combineOp refs)).eventTrace path.2.2.2))
      = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    NatModCheck.into_events, BitWord.bitWord_instruction_eventTrace]
  rfl

/-- The actual positive suffix meets the original independent envelope with equality. -/
lemma positiveInto_resourcePool (refs : Refs ctx shortWidth)
    (path : (positiveInto refs).Path) :
    (positiveInto refs).resourcePool path = positiveEventEnvelope shortWidth := by
  change ResourcePool.ofList ((positiveInto refs).eventTrace path) = _
  rw [positiveInto_events]
  simp only [positiveTrace, positiveEventEnvelope, NatModCheck.eventEnvelope,
    ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero, add_assoc]

/-- Every actual positive suffix respects the independent native coordinate bound. -/
lemma positiveInto_pool_le (refs : Refs ctx shortWidth) (path : (positiveInto refs).Path) :
    (positiveInto refs).resourcePool path ≤ positiveEventEnvelope shortWidth :=
  le_of_eq (positiveInto_resourcePool refs path)

/-- Every positive suffix performs exactly five actual native operations. -/
lemma positiveInto_eventCount (refs : Refs ctx shortWidth) (path : (positiveInto refs).Path) :
    ((positiveInto refs).eventTrace path).length = 5 := rfl

/-- Five dependent native operations give the positive suffix exact unit-duration depth five. -/
lemma positiveInto_depth (refs : Refs ctx shortWidth) (path : (positiveInto refs).Path) :
    (positiveInto refs).depth (fun _ => 1) path = 5 := rfl

/-- The positive suffix visits only the original complete context at its five instructions. -/
lemma positiveInto_visited (refs : Refs ctx shortWidth) (path : (positiveInto refs).Path) :
    (positiveInto refs).visitedContexts path = List.replicate 5 ctx := rfl

/-- Positive-suffix resident accounting includes all original caller storage. -/
lemma positiveInto_resident_le (refs : Refs ctx shortWidth) (path : (positiveInto refs).Path) :
    (positiveInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [positiveInto_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- Positive-suffix auxiliary accounting preserves all supplied workspace roles. -/
lemma positiveInto_auxiliary_le (refs : Refs ctx shortWidth) (path : (positiveInto refs).Path) :
    (positiveInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [positiveInto_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- The positive suffix restores the full borrowed-reference joint state. -/
lemma positiveInto_borrowedRestored (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (positiveInto refs).BorrowedRestored Reference state
      ((positiveInto refs).execute environment Reference state) := by
  refine Circuit.borrowedRestored_seq (environment := environment) _ _ state
    (Circuit.borrowedRestored_classical (environment := environment)
      (BitWord.selectedApplication (execution := model) (widenOp refs)) state) ?_
  refine Circuit.borrowedRestored_seq (environment := environment) _ _ _
    (Circuit.borrowedRestored_classical (environment := environment)
      (BitWord.selectedApplication (execution := model) (belowOp refs)) _) ?_
  exact Circuit.borrowedRestored_seq (environment := environment) _ _ _
    (NatModCheck.into_borrowedRestored refs.modulusCheck Reference _)
    (Circuit.borrowedRestored_classical (environment := environment)
      (BitWord.selectedApplication (execution := model) (combineOp refs)) _)

/-- The total trace contains its real decision and only the selected branch's native events. -/
lemma into_events (refs : TotalRefs ctx shortWidth) (path : (into refs).Path) :
    (into refs).eventTrace path = nativeTrace shortWidth path.2.1.toBool := by
  rcases path with ⟨decision, flag, selected⟩
  cases flag with
  | bit flag =>
      cases flag with
      | false =>
          change (BitWord.instruction (execution := model) (rejectOp refs)).Path at selected
          change (BitWord.instruction (execution := model) (decisionOp refs)).eventTrace
            decision ++
              (BitWord.instruction (execution := model) (rejectOp refs)).eventTrace selected = _
          rw [BitWord.bitWord_instruction_eventTrace,
            BitWord.bitWord_instruction_eventTrace]
          rfl
      | true =>
          change (positiveInto refs.positiveCheck).Path at selected
          change (BitWord.instruction (execution := model) (decisionOp refs)).eventTrace
            decision ++ (positiveInto refs.positiveCheck).eventTrace selected = _
          rw [BitWord.bitWord_instruction_eventTrace, positiveInto_events]
          rfl

/-- Actual total-check multiplicities are those of the same selected chronological formula. -/
lemma into_resourcePool (refs : TotalRefs ctx shortWidth) (path : (into refs).Path) :
    (into refs).resourcePool path = ResourcePool.ofList (nativeTrace shortWidth path.2.1.toBool) :=
  congrArg ResourcePool.ofList (into_events refs path)

/-- Every total-check path satisfies the original independent maximum-branch envelope. -/
lemma into_pool_le (refs : TotalRefs ctx shortWidth) (path : (into refs).Path) :
    (into refs).resourcePool path ≤ eventEnvelope shortWidth := by
  rw [into_resourcePool]
  cases selected : path.2.1.toBool
  · simp only [nativeTrace, Bool.false_eq_true, if_false, ResourcePool.ofList_cons,
      ResourcePool.ofList_nil, add_zero, eventEnvelope]
    exact add_le_add le_rfl (ResourcePool.le_max_right _ _)
  · simp only [nativeTrace, if_true, ResourcePool.ofList_cons]
    have positive : ResourcePool.ofList (positiveTrace shortWidth) =
        (positiveEventEnvelope shortWidth : ResourcePool model) := by
      simp only [positiveTrace, positiveEventEnvelope, NatModCheck.eventEnvelope,
        ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero, add_assoc]
    rw [positive]
    exact add_le_add le_rfl (ResourcePool.le_max_left _ _)

/-- The total checker performs six native operations when selected and two when rejected. -/
lemma into_eventCount (refs : TotalRefs ctx shortWidth) (path : (into refs).Path) :
    ((into refs).eventTrace path).length = if path.2.1.toBool then 6 else 2 := by
  rcases path with ⟨decision, flag, selected⟩
  cases flag with
  | bit flag => cases flag <;> rfl

/-- Actual total depth includes the decision before all operations in its selected branch. -/
lemma into_depth (refs : TotalRefs ctx shortWidth) (path : (into refs).Path) :
    (into refs).depth (fun _ => 1) path = if path.2.1.toBool then 6 else 2 := by
  rcases path with ⟨decision, flag, selected⟩
  cases flag with
  | bit flag => cases flag <;> rfl

/-- Independent total-check unit-duration dependency depth bound. -/
lemma into_depth_le (refs : TotalRefs ctx shortWidth) (path : (into refs).Path) :
    (into refs).depth (fun _ => 1) path ≤ 6 := by
  rw [into_depth]
  split <;> omega

/-- Every selected total-check instruction keeps the complete caller context live. -/
lemma into_visited (refs : TotalRefs ctx shortWidth) (path : (into refs).Path) :
    (into refs).visitedContexts path =
      List.replicate (if path.2.1.toBool then 6 else 2) ctx := by
  rcases path with ⟨decision, flag, selected⟩
  cases flag with
  | bit flag => cases flag <;> rfl

/-- Every actual total-check path retains all original resident storage. -/
lemma into_resident_le (refs : TotalRefs ctx shortWidth) (path : (into refs).Path) :
    (into refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- Every actual total-check path retains all original auxiliary storage. -/
lemma into_auxiliary_le (refs : TotalRefs ctx shortWidth) (path : (into refs).Path) :
    (into refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- Decision and actual selected body restore the complete borrowed-reference joint state. -/
lemma into_borrowedRestored (refs : TotalRefs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into refs).BorrowedRestored
      Reference state ((into refs).execute environment Reference state) := by
  refine Circuit.borrowedRestored_seq (environment := environment) _ _ state
    (Circuit.borrowedRestored_classical (environment := environment)
      (BitWord.selectedApplication (execution := model) (decisionOp refs)) state) ?_
  apply Circuit.borrowedRestored_branch
    (environment := environment) (writeInput refs.greaterThanOne) (arm refs) Reference
  intro flag history _ current
  cases flag with
  | bit flag =>
      cases flag with
      | false =>
          exact Circuit.borrowedRestored_classical (environment := environment)
            (BitWord.selectedApplication (execution := model) (rejectOp refs)) current
      | true => exact positiveInto_borrowedRestored refs.positiveCheck Reference current

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidateCheck
