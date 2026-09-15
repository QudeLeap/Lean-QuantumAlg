/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Selection.Correctness

/-!
# Actual candidate eligibility and direct-selection resources
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSelector

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent native trace of the original two eligibility conjunctions. -/
def eligibilityTrace : List (Resource.Event kind) :=
  [.classicalOperation (.bit .and), .classicalOperation (.bit .and)]

/-- Independent allowance for both original conjunctions and the two possible persistent copies. -/
def candidateSelectorEventEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.ofList eligibilityTrace +
    ResourcePool.ofList (ClassicalRoutines.FirstAccepted.Direct.copyTrace width)

/-- Both original actual eligibility instructions precede precisely the selected native copy arm. -/
theorem candidateSelectorInto_events (refs : Refs ctx width)
    (path : (candidateSelectorInto refs).Path) :
    (candidateSelectorInto refs).eventTrace path =
      eligibilityTrace ++ (selectionInto refs).eventTrace path.2 := rfl

/-- The actual closing suffix fits the independent native allowance for its four possible writes. -/
theorem candidateSelectorInto_pool_le (refs : Refs ctx width)
    (path : (candidateSelectorInto refs).Path) :
    (candidateSelectorInto refs).resourcePool path ≤ candidateSelectorEventEnvelope kind width := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add le_rfl (ClassicalRoutines.FirstAccepted.Direct.into_pool_le
    (writeInput refs.eligible) refs.candidate refs.selection path.2)

/-- The original two actual eligibility operations have exactly two unit durations. -/
theorem candidateEligibilityInto_depth (refs : Refs ctx width)
    (path : (candidateEligibilityInto refs).Path) :
    (candidateEligibilityInto refs).depth (fun _ => 1) path = 2 := rfl

/-- Actual depth includes eligibility-to-selection dependencies and at most four native writes. -/
theorem candidateSelectorInto_depth_le (refs : Refs ctx width)
    (path : (candidateSelectorInto refs).Path) :
    (candidateSelectorInto refs).depth (fun _ => 1) path ≤ 4 := by
  have selected := ClassicalRoutines.FirstAccepted.Direct.into_depth_le
    (writeInput refs.eligible) refs.candidate refs.selection path.2
  change 2 + (ClassicalRoutines.FirstAccepted.Direct.into
    (writeInput refs.eligible) refs.candidate refs.selection).depth (fun _ => 1) path.2 ≤ 4
  omega

/-- The actual original conjunctions restore the complete borrowed-reference joint state. -/
theorem candidateEligibilityInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (candidateEligibilityInto refs).BorrowedRestored Reference state
      ((candidateEligibilityInto refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (Circuit.borrowedRestored_classical _ state)
    (Circuit.borrowedRestored_classical _ _)

/-- Actual candidate selection preserves every borrowed system and external reference jointly. -/
theorem candidateSelectorInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (candidateSelectorInto refs).BorrowedRestored Reference state
      ((candidateSelectorInto refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (candidateEligibilityInto_borrowedRestored refs Reference state)
    (ClassicalRoutines.FirstAccepted.Direct.into_borrowedRestored
      (writeInput refs.eligible) refs.candidate refs.selection Reference _)

/-- All original eligibility and direct-selection instructions visit only the supplied context. -/
theorem candidateSelectorInto_visited (refs : Refs ctx width)
    (path : (candidateSelectorInto refs).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (candidateSelectorInto refs).visitedContexts path) : visited = ctx := by
  change visited ∈ [ctx, ctx] ++ (selectionInto refs).visitedContexts path.2 at present
  rcases List.mem_append.mp present with eligible | selected
  · simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using eligible
  · exact ClassicalRoutines.FirstAccepted.Direct.into_visited
      (writeInput refs.eligible) refs.candidate refs.selection path.2 visited selected

/-- Actual selection keeps every caller resource counted without allocating selector work bits. -/
theorem candidateSelectorInto_resident_le (refs : Refs ctx width)
    (path : (candidateSelectorInto refs).Path) :
    (candidateSelectorInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [candidateSelectorInto_visited refs path visited present]

/-- All original auxiliary roles remain charged throughout the complete actual suffix. -/
theorem candidateSelectorInto_auxiliary_le (refs : Refs ctx width)
    (path : (candidateSelectorInto refs).Path) :
    (candidateSelectorInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [candidateSelectorInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSelector
