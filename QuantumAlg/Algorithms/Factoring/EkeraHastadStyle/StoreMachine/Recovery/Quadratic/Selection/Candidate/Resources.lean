/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Selection.Candidate.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Check.Resources
import all QuantumAlg.Components.Classical.FirstAccepted.Resources
import all QuantumAlg.Components.Classical.FirstAccepted.Preservation

/-!
# Independent native resources and joint restoration of checked selection

The check and selector use their own actual stored branch decisions. Their
sequential composition charges every selected native event, retains all caller
storage, and restores the complete borrowed-reference joint state.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidateSelect

open Execution
open ClassicalRoutines

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {shortWidth : Nat}

/-- Independent original check allowance plus the four-operation selector allowance. -/
def eventEnvelope (shortWidth : Nat) : ResourcePool model :=
  QuadraticCandidateCheck.eventEnvelope shortWidth +
    FirstAccepted.nativeEnvelope model (QuadraticCandidateCheck.CandidateWidth shortWidth)

/-- Chronological native formula on the two actual recorded decisions. -/
def nativeTrace (shortWidth : Nat) (positive taken : Bool) : List (Resource.Event model) :=
  QuadraticCandidateCheck.nativeTrace shortWidth positive ++
    (FirstAccepted.decisionEvents model ++
      if taken then FirstAccepted.copyEvents model
        (QuadraticCandidateCheck.CandidateWidth shortWidth) else [])

/-- The exact native trace contains the check path and selected selector arm in order. -/
theorem into_events (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).eventTrace path =
      nativeTrace shortWidth path.1.2.1.toBool path.2.2.1.toBool := by
  change (QuadraticCandidateCheck.into refs.check).eventTrace path.1 ++
    (FirstAccepted.circuit (selectionInputs refs) refs.selection).eventTrace path.2 = _
  rw [QuadraticCandidateCheck.into_events, FirstAccepted.firstAccepted_eventTrace]
  rfl

/-- Actual native multiplicities are those of the same independently described trace. -/
theorem into_resourcePool (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).resourcePool path =
      ResourcePool.ofList (nativeTrace shortWidth path.1.2.1.toBool path.2.2.1.toBool) :=
  congrArg ResourcePool.ofList (into_events refs path)

/-- Every actual path satisfies the sum of the original independent component budgets. -/
theorem into_pool_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).resourcePool path ≤ eventEnvelope shortWidth := by
  change ResourcePool.ofList ((QuadraticCandidateCheck.into refs.check).eventTrace path.1 ++
    (FirstAccepted.circuit (selectionInputs refs) refs.selection).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (QuadraticCandidateCheck.into_pool_le refs.check path.1)
    (FirstAccepted.firstAccepted_pool_le (selectionInputs refs) refs.selection path.2)

/-- Exact native operation count keeps both actual branch choices. -/
theorem into_eventCount (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    ((into refs).eventTrace path).length =
      (if path.1.2.1.toBool then 6 else 2) + (if path.2.2.1.toBool then 4 else 2) := by
  rw [into_events]
  unfold nativeTrace QuadraticCandidateCheck.nativeTrace
  cases path.1.2.1.toBool <;> cases path.2.2.1.toBool <;> rfl

/-- Unit-duration depth charges the check before the selector's decision and optional copies. -/
theorem into_depth (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).depth (fun _ => 1) path =
      (if path.1.2.1.toBool then 6 else 2) + (if path.2.2.1.toBool then 4 else 2) := by
  change (QuadraticCandidateCheck.into refs.check).depth (fun _ => 1) path.1 +
    (FirstAccepted.circuit (selectionInputs refs) refs.selection).depth (fun _ => 1) path.2 = _
  rw [QuadraticCandidateCheck.into_depth, FirstAccepted.firstAccepted_unit_depth]

/-- Independent ten-operation unit-duration dependency depth allowance. -/
theorem into_depth_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).depth (fun _ => 1) path ≤ 10 := by
  rw [into_depth]
  split <;> split <;> omega

/-- Every actually visited context is the complete existing caller context. -/
theorem into_visited (refs : Refs ctx shortWidth) (path : (into refs).Path)
    (visited : RuntimeCtx model.kind) (present : visited ∈ (into refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (QuadraticCandidateCheck.into refs.check).visitedContexts path.1 ++
    (FirstAccepted.circuit (selectionInputs refs) refs.selection).visitedContexts path.2 at present
  rcases List.mem_append.mp present with checkPresent | selectPresent
  · rw [QuadraticCandidateCheck.into_visited] at checkPresent
    exact (List.mem_replicate.mp checkPresent).2
  · exact FirstAccepted.firstAccepted_visited _ _ _ _ selectPresent

/-- The actual composition keeps every supplied classical cell and quantum dimension resident. -/
theorem into_resident_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- All existing workspace roles remain included in the same actual auxiliary peak. -/
theorem into_auxiliary_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- Complete borrowed restoration composes across the real check and canonical selector. -/
theorem into_borrowedRestored (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into refs).BorrowedRestored Reference state ((into refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (QuadraticCandidateCheck.into_borrowedRestored refs.check Reference state)
    (FirstAccepted.firstAccepted_borrowedRestored (selectionInputs refs) refs.selection Reference _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidateSelect
