/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Program
import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Initialize.Resources
import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Rounds.Resources

/-!
# Independent native budgets of the actual natural-square-root driver

The budget charges actual initialization, all finite refinement rounds and
the final caller-output copy. All paths use the same caller-supplied storage.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {inputWidth : Nat}

/-- The original independent initialization, refinement and final-copy native formula. -/
def eventEnvelope (inputWidth : Nat) : ResourcePool kind :=
  initializationEventEnvelope inputWidth +
    (ResourcePool.scale inputWidth
        (ResourcePool.ofList (IntegerSqrt.roundTrace (workWidth inputWidth))) +
      ResourcePool.singleton (.classicalOperation (.wordUnary .copy (workWidth inputWidth))))

/-- Exact chronological native instruction formula independent of caller store and path. -/
def driverTrace (inputWidth : Nat) : List (Resource.Event kind) :=
  initializationTrace inputWidth ++ roundsTrace inputWidth inputWidth ++
    [.classicalOperation (.wordUnary .copy (workWidth inputWidth))]

/-- The complete actual trace includes the caller-output copy after all refinement rounds. -/
theorem into_events (refs : Refs ctx inputWidth) (path : (into refs).Path) :
    (into refs).eventTrace path = driverTrace inputWidth := by
  rcases path with ⟨initPath, roundPath, finishPath⟩
  change (initializeInto refs).eventTrace initPath ++
    ((roundsInto refs inputWidth).eventTrace roundPath ++
      [.classicalOperation (.wordUnary .copy (workWidth inputWidth))]) = _
  rw [initializeInto_events, roundsInto_events]
  exact List.append_assoc _ _ _ |>.symm

/-- The same actual path has exactly the independently specified native coordinates. -/
theorem into_resourcePool (refs : Refs ctx inputWidth) (path : (into refs).Path) :
    (into refs).resourcePool path = eventEnvelope inputWidth := by
  rcases path with ⟨initPath, roundPath, finishPath⟩
  change ResourcePool.ofList ((initializeInto refs).eventTrace initPath ++
    ((roundsInto refs inputWidth).eventTrace roundPath ++
      [.classicalOperation (.wordUnary .copy (workWidth inputWidth))])) = _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  change (initializeInto refs).resourcePool initPath +
    ((roundsInto refs inputWidth).resourcePool roundPath + _) = _
  rw [initializeInto_resourcePool, roundsInto_resourcePool]
  rfl

/-- Every actual driver path satisfies the independent original native budget. -/
theorem into_pool_le (refs : Refs ctx inputWidth) (path : (into refs).Path) :
    (into refs).resourcePool path ≤ eventEnvelope inputWidth :=
  le_of_eq (into_resourcePool refs path)

/-- The actual event count includes every setup write, shift, refinement and final copy. -/
theorem into_eventCount (refs : Refs ctx inputWidth) (path : (into refs).Path) :
    ((into refs).eventTrace path).length = 4 + (inputWidth - 1) + (inputWidth * 6 + 1) := by
  rcases path with ⟨initPath, roundPath, finishPath⟩
  change ((initializeInto refs).eventTrace initPath ++
    ((roundsInto refs inputWidth).eventTrace roundPath ++ [_])).length = _
  rw [List.length_append, List.length_append, initializeInto_eventCount, roundsInto_eventCount]
  rfl

/-- Actual unit-duration depth retains all dependencies through the final output write. -/
theorem into_depth (refs : Refs ctx inputWidth) (path : (into refs).Path) :
    (into refs).depth (fun _ => 1) path = 4 + (inputWidth - 1) + (inputWidth * 6 + 1) := by
  rcases path with ⟨initPath, roundPath, finishPath⟩
  change (initializeInto refs).depth (fun _ => 1) initPath +
    ((roundsInto refs inputWidth).depth (fun _ => 1) roundPath + 1) = _
  rw [initializeInto_depth, roundsInto_depth]

/-- The complete original context is retained at every actual driver instruction. -/
theorem into_visited (refs : Refs ctx inputWidth) (path : (into refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (into refs).visitedContexts path) :
    visited = ctx := by
  rcases path with ⟨initPath, roundPath, finishPath⟩
  change visited ∈ (initializeInto refs).visitedContexts initPath ++
    ((roundsInto refs inputWidth).visitedContexts roundPath ++ [ctx]) at present
  rcases List.mem_append.mp present with initPresent | tailPresent
  · exact initializeInto_visited refs initPath visited initPresent
  · rcases List.mem_append.mp tailPresent with roundPresent | finishPresent
    · exact roundsInto_visited refs inputWidth roundPath visited roundPresent
    · exact List.mem_singleton.mp finishPresent

/-- Resident peak counts all original caller-supplied classical and quantum storage. -/
theorem into_resident_le (refs : Refs ctx inputWidth) (path : (into refs).Path) :
    (into refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- Auxiliary peak counts the original roles through initialization, iteration and copy. -/
theorem into_auxiliary_le (refs : Refs ctx inputWidth) (path : (into refs).Path) :
    (into refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- The complete actual driver restores borrowed storage jointly with arbitrary references. -/
theorem into_borrowedRestored (refs : Refs ctx inputWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into refs).BorrowedRestored Reference state ((into refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact initializeInto_borrowedRestored refs Reference state
  · apply Circuit.borrowedRestored_seq
    · exact roundsInto_borrowedRestored refs inputWidth Reference _
    · exact Circuit.borrowedRestored_classical (finishOp refs) _

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt
