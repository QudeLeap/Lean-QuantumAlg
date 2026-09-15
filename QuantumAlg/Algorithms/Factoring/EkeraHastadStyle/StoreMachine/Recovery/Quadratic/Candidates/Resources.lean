/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Candidates.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Candidates.Prefix.Resources
import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sub.Resources

/-!
# Independent quadratic-candidate native budgets and joint borrowed restoration
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidates

open Execution
open ClassicalRoutines.NumberTheory

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}

/-- Two original width conversions before the actual candidate arithmetic. -/
def resizeTrace (shortWidth : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordResize (QuadraticPrefix.centerWidth shortWidth)
      (candidateWidth shortWidth)),
    .classicalOperation (.wordResize (QuadraticPrefix.discriminantWidth shortWidth)
      (candidateWidth shortWidth))]

/-- Independent five-operation suffix formula, including the selected subtraction branch. -/
def suffixTrace (shortWidth : Nat) (underflow : Bool) : List (Resource.Event kind) :=
  resizeTrace shortWidth ++ NatSub.nativeTrace (candidateWidth shortWidth) underflow ++
    [.classicalOperation (.addCarry (candidateWidth shortWidth))]

/-- Placement-independent allowance for both conversions and the original candidate arithmetic. -/
def suffixEnvelope (shortWidth : Nat) : ResourcePool kind :=
  (ResourcePool.ofList (resizeTrace shortWidth) +
    NatSub.eventEnvelope (candidateWidth shortWidth)) +
    ResourcePool.singleton (.classicalOperation (.addCarry (candidateWidth shortWidth)))

/-- The actual suffix path emits exactly the independently specified five native instructions. -/
theorem suffixInto_events (refs : Refs ctx shortWidth) (path : (suffixInto refs).Path) :
    (suffixInto refs).eventTrace path =
      suffixTrace shortWidth path.2.2.1.2.1.toBool := by
  change resizeTrace shortWidth ++ (NatSub.into refs.first).eventTrace path.2.2.1 ++
    [.classicalOperation (.addCarry (candidateWidth shortWidth))] = _
  rw [NatSub.into_events]
  rfl

/-- Every actual suffix branch meets the original independent native coordinate allowance. -/
theorem suffixInto_pool_le (refs : Refs ctx shortWidth) (path : (suffixInto refs).Path) :
    (suffixInto refs).resourcePool path ≤ suffixEnvelope shortWidth := by
  change ResourcePool.ofList (resizeTrace shortWidth ++
    (NatSub.into refs.first).eventTrace path.2.2.1 ++
      [.classicalOperation (.addCarry (candidateWidth shortWidth))]) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add (add_le_add le_rfl (NatSub.into_pool_le refs.first path.2.2.1)) le_rfl

/-- Both candidate writes and the real comparison are charged in addition to the resizes. -/
theorem suffixInto_eventCount (refs : Refs ctx shortWidth) (path : (suffixInto refs).Path) :
    ((suffixInto refs).eventTrace path).length = 5 := by
  rw [suffixInto_events]
  simp only [suffixTrace, List.length_append, NatSub.nativeTrace]
  rfl

/-- Original sequential dependencies give the five native suffix instructions depth five. -/
theorem suffixInto_depth (refs : Refs ctx shortWidth) (path : (suffixInto refs).Path) :
    (suffixInto refs).depth (fun _ => 1) path = 5 := by
  change 1 + (1 + ((NatSub.into refs.first).depth (fun _ => 1) path.2.2.1 + 1)) = _
  rw [NatSub.into_depth]

/-- Every suffix instruction keeps the complete supplied runtime context live. -/
theorem suffixInto_visited (refs : Refs ctx shortWidth) (path : (suffixInto refs).Path) :
    (suffixInto refs).visitedContexts path = List.replicate 5 ctx := by
  change [ctx, ctx] ++ (NatSub.into refs.first).visitedContexts path.2.2.1 ++ [ctx] = _
  rw [NatSub.into_visited]
  rfl

/-- Every actual suffix operation restores borrowed storage jointly with external references. -/
theorem suffixInto_borrowedRestored (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (suffixInto refs).BorrowedRestored Reference state
      ((suffixInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact Circuit.borrowedRestored_classical (centerOp refs) state
  · apply Circuit.borrowedRestored_seq
    · exact Circuit.borrowedRestored_classical (rootOp refs) _
    · exact Circuit.borrowedRestored_seq _ _ _
        (NatSub.into_borrowedRestored refs.first Reference _)
        (Circuit.borrowedRestored_classical (secondOp refs) _)

/-- The complete original formula accounts for the actual discriminant and candidate branches. -/
def nativeTrace (shortWidth : Nat) (discriminantUnderflow candidateUnderflow : Bool) :
    List (Resource.Event kind) :=
  QuadraticPrefix.nativeTrace shortWidth discriminantUnderflow ++
    suffixTrace shortWidth candidateUnderflow

/-- The complete native allowance is specified independently of every execution record. -/
def eventEnvelope (shortWidth : Nat) : ResourcePool kind :=
  QuadraticPrefix.eventEnvelope shortWidth + suffixEnvelope shortWidth

/-- Prefix, square-root refinement and both candidate instructions share one actual path. -/
theorem into_events (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).eventTrace path =
      nativeTrace shortWidth path.1.1.2.2.1.toBool path.2.2.2.1.2.1.toBool := by
  change (QuadraticPrefix.into refs.quadraticPrefix).eventTrace path.1 ++
    (suffixInto refs).eventTrace path.2 = _
  rw [QuadraticPrefix.into_events, suffixInto_events]
  rfl

/-- The complete native multiplicities are counted from that same actual execution path. -/
theorem into_resourcePool (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).resourcePool path = ResourcePool.ofList
      (nativeTrace shortWidth path.1.1.2.2.1.toBool path.2.2.2.1.2.1.toBool) :=
  congrArg ResourcePool.ofList (into_events refs path)

/-- The actual complete native coordinates meet the independent original allowance. -/
theorem into_pool_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).resourcePool path ≤ eventEnvelope shortWidth := by
  change ResourcePool.ofList ((QuadraticPrefix.into refs.quadraticPrefix).eventTrace path.1 ++
    (suffixInto refs).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (QuadraticPrefix.into_pool_le refs.quadraticPrefix path.1)
    (suffixInto_pool_le refs path.2)

/-- Every instruction is charged, including square-root initialization and both candidates. -/
theorem into_eventCount (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    ((into refs).eventTrace path).length =
      7 * QuadraticPrefix.discriminantWidth shortWidth + 14 := by
  change ((QuadraticPrefix.into refs.quadraticPrefix).eventTrace path.1 ++
    (suffixInto refs).eventTrace path.2).length = _
  rw [List.length_append, QuadraticPrefix.into_eventCount, suffixInto_eventCount]

/-- The complete original sequential dependency depth follows the same explicit width formula. -/
theorem into_depth (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).depth (fun _ => 1) path =
      7 * QuadraticPrefix.discriminantWidth shortWidth + 14 := by
  change (QuadraticPrefix.into refs.quadraticPrefix).depth (fun _ => 1) path.1 +
    (suffixInto refs).depth (fun _ => 1) path.2 = _
  rw [QuadraticPrefix.into_depth, suffixInto_depth]

/-- Every supplied classical cell and quantum system remains live through candidate construction. -/
theorem into_visited (refs : Refs ctx shortWidth) (path : (into refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (into refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (QuadraticPrefix.into refs.quadraticPrefix).visitedContexts path.1 ++
    (suffixInto refs).visitedContexts path.2 at present
  rcases List.mem_append.mp present with prefixPresent | suffixPresent
  · exact QuadraticPrefix.into_visited refs.quadraticPrefix path.1 visited prefixPresent
  · rw [suffixInto_visited] at suffixPresent
    exact (List.mem_replicate.mp suffixPresent).2

/-- Resident accounting includes the complete caller context throughout the actual circuit. -/
theorem into_resident_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- Auxiliary accounting includes all original workspace roles without a hidden allocation. -/
theorem into_auxiliary_le (refs : Refs ctx shortWidth) (path : (into refs).Path) :
    (into refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- Complete execution restores borrowed systems jointly with arbitrary external references. -/
theorem into_borrowedRestored (refs : Refs ctx shortWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into refs).BorrowedRestored Reference state ((into refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact QuadraticPrefix.into_borrowedRestored refs.quadraticPrefix Reference state
  · exact suffixInto_borrowedRestored refs Reference _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidates
