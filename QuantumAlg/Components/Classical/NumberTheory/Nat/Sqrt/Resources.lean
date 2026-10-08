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

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {inputWidth : Nat}

/-- The original independent initialization, refinement and final-copy native formula. -/
def eventEnvelope (inputWidth : Nat) : ResourcePool model :=
  initializationEventEnvelope (model := model) inputWidth +
    (ResourcePool.scale inputWidth
        (ResourcePool.ofList (IntegerSqrt.roundTrace (model := model) (workWidth inputWidth))) +
      ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy (workWidth inputWidth)))))

/-- Exact chronological native instruction formula independent of caller store and path. -/
def driverTrace (inputWidth : Nat) : List (Resource.Event model) :=
  initializationTrace (model := model) inputWidth ++ roundsTrace (model := model) inputWidth
    inputWidth ++
    [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy (workWidth inputWidth)))]

/-- The complete actual trace includes the caller-output copy after all refinement rounds. -/
theorem into_events (refs : Refs ctx inputWidth) (path : (into (model := model) refs).Path) :
    (into (model := model) refs).eventTrace path = driverTrace (model := model) inputWidth := by
  rcases path with ⟨initPath, roundPath, finishPath⟩
  change (BitWord.instruction (execution := model) (finishOp refs)).Path at finishPath
  change (initializeInto (model := model) refs).eventTrace initPath ++
    ((roundsInto (model := model) refs inputWidth).eventTrace roundPath ++
      (finishInto (model := model) refs).eventTrace finishPath) = _
  rw [initializeInto_events, roundsInto_events]
  change _ ++ (_ ++ (BitWord.instruction (execution := model)
    (finishOp refs)).eventTrace finishPath) = _
  rw [BitWord.bitWord_instruction_eventTrace]
  exact List.append_assoc _ _ _ |>.symm

/-- The same actual path has exactly the independently specified native coordinates. -/
theorem into_resourcePool (refs : Refs ctx inputWidth) (path : (into (model := model) refs).Path) :
    (into (model := model) refs).resourcePool path = eventEnvelope (model := model) inputWidth := by
  rcases path with ⟨initPath, roundPath, finishPath⟩
  change (BitWord.instruction (execution := model) (finishOp refs)).Path at finishPath
  change ResourcePool.ofList ((initializeInto (model := model) refs).eventTrace initPath ++
    ((roundsInto (model := model) refs inputWidth).eventTrace roundPath ++
      (finishInto (model := model) refs).eventTrace finishPath)) = _
  change ResourcePool.ofList (_ ++ (_ ++ (BitWord.instruction (execution := model)
    (finishOp refs)).eventTrace finishPath)) = _
  rw [BitWord.bitWord_instruction_eventTrace, ResourcePool.ofList_append,
    ResourcePool.ofList_append]
  change (initializeInto (model := model) refs).resourcePool initPath +
    ((roundsInto (model := model) refs inputWidth).resourcePool roundPath + _) = _
  rw [initializeInto_resourcePool, roundsInto_resourcePool]
  rfl

/-- Every actual driver path satisfies the independent original native budget. -/
theorem into_pool_le (refs : Refs ctx inputWidth) (path : (into (model := model) refs).Path) :
    (into (model := model) refs).resourcePool path ≤ eventEnvelope (model := model) inputWidth :=
  le_of_eq (into_resourcePool refs path)

/-- The actual event count includes every setup write, shift, refinement and final copy. -/
theorem into_eventCount (refs : Refs ctx inputWidth) (path : (into (model := model) refs).Path) :
    ((into (model := model) refs).eventTrace path).length = 4 + (inputWidth - 1) + (inputWidth * 6
      + 1) := by
  rcases path with ⟨initPath, roundPath, finishPath⟩
  change (BitWord.instruction (execution := model) (finishOp refs)).Path at finishPath
  change ((initializeInto (model := model) refs).eventTrace initPath ++
    ((roundsInto (model := model) refs inputWidth).eventTrace roundPath ++
      (BitWord.instruction (execution := model) (finishOp refs)).eventTrace finishPath)).length = _
  rw [BitWord.bitWord_instruction_eventTrace, List.length_append, List.length_append,
    initializeInto_eventCount, roundsInto_eventCount]
  rfl

/-- Actual unit-duration depth retains all dependencies through the final output write. -/
theorem into_depth (refs : Refs ctx inputWidth) (path : (into (model := model) refs).Path) :
    (into (model := model) refs).depth (fun _ => 1) path = 4 + (inputWidth - 1) + (inputWidth * 6
      + 1) := by
  rcases path with ⟨initPath, roundPath, finishPath⟩
  change (initializeInto (model := model) refs).depth (fun _ => 1) initPath +
    ((roundsInto (model := model) refs inputWidth).depth (fun _ => 1) roundPath + 1) = _
  rw [initializeInto_depth, roundsInto_depth]

/-- The complete original context is retained at every actual driver instruction. -/
theorem into_visited (refs : Refs ctx inputWidth) (path : (into (model := model) refs).Path)
    (visited : RuntimeCtx model.kind) (present : visited ∈ (into (model := model)
      refs).visitedContexts path) :
    visited = ctx := by
  rcases path with ⟨initPath, roundPath, finishPath⟩
  change visited ∈ (initializeInto (model := model) refs).visitedContexts initPath ++
    ((roundsInto (model := model) refs inputWidth).visitedContexts roundPath ++ [ctx]) at present
  rcases List.mem_append.mp present with initPresent | tailPresent
  · exact initializeInto_visited refs initPath visited initPresent
  · rcases List.mem_append.mp tailPresent with roundPresent | finishPresent
    · exact roundsInto_visited refs inputWidth roundPath visited roundPresent
    · exact List.mem_singleton.mp finishPresent

/-- Resident peak counts all original caller-supplied classical and quantum storage. -/
theorem into_resident_le (refs : Refs ctx inputWidth) (path : (into (model := model) refs).Path) :
    (into (model := model) refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- Auxiliary peak counts the original roles through initialization, iteration and copy. -/
theorem into_auxiliary_le (refs : Refs ctx inputWidth) (path : (into (model := model) refs).Path) :
    (into (model := model) refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited refs path visited present]

/-- The complete actual driver restores borrowed storage jointly with arbitrary references. -/
theorem into_borrowedRestored (refs : Refs ctx inputWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) refs).BorrowedRestored Reference state ((into (model := model)
      refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact initializeInto_borrowedRestored refs Reference state
  · apply Circuit.borrowedRestored_seq
    · exact roundsInto_borrowedRestored refs inputWidth Reference _
    · exact Circuit.borrowedRestored_classical
        (BitWord.selectedApplication (execution := model) (finishOp refs)) _

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt
