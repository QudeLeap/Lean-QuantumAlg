/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Word.Split
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Actual native word-split resources

The independent formula has one low resize, the prescribed number of native
one-bit shifts, and one high resize. Every actual path has exactly that count
and unit-duration depth, keeps the supplied context, and restores all borrowed
correlations jointly with external references.
-/

namespace QuantumAlg.ClassicalRoutines.Word.Split

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width highWidth lowWidth : Nat}

/-- Independent native formula for the prescribed number of one-bit shifts. -/
def shiftTrace (width count : Nat) : List (Resource.Event model) :=
  List.replicate count (.classicalOperation
    (BitWord.selectedCoordinate (execution := model) (.wordUnary .shiftRight width)))

/-- Independent low-resize, native shifts, high-resize formula. -/
def splitTrace (highWidth lowWidth : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize (highWidth + lowWidth) lowWidth))] ++
    (shiftTrace (model := model) (highWidth + lowWidth) lowWidth ++
      [.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordResize (highWidth + lowWidth) highWidth))])

/-- Every actual shift path emits exactly the independent replicated native instruction. -/
theorem shiftInto_events (count : Nat) (work : CWriteRef ctx (.unsignedWord width))
    (path : (shiftInto (model := model) count work).Path) :
    (shiftInto (model := model) count work).eventTrace path =
      shiftTrace (model := model) width count := by
  change (List.ofFn (fun index : Fin count =>
    (BitWord.instruction (execution := model) (shiftOp work)).eventTrace
      (path index))).flatten = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  simp [shiftTrace, shiftOp, ClassicalOp.label]

/-- Every actual word-split path emits the independent complete native formula. -/
theorem splitInto_events (refs : Refs ctx highWidth lowWidth)
    (path : (splitInto (model := model) refs).Path) :
    (splitInto (model := model) refs).eventTrace path =
      splitTrace (model := model) highWidth lowWidth := by
  change (BitWord.instruction (execution := model) (lowOp refs)).eventTrace path.1 ++
    ((shiftInto (model := model) lowWidth refs.work).eventTrace path.2.1 ++
      (BitWord.instruction (execution := model) (highOp refs)).eventTrace path.2.2) = _
  rw [BitWord.bitWord_instruction_eventTrace, shiftInto_events,
    BitWord.bitWord_instruction_eventTrace]
  rfl

/-- Actual native multiplicities equal the independent complete word-split formula. -/
theorem splitInto_resourcePool (refs : Refs ctx highWidth lowWidth)
    (path : (splitInto (model := model) refs).Path) :
    (splitInto (model := model) refs).resourcePool path =
      ResourcePool.ofList (splitTrace (model := model) highWidth lowWidth) :=
  congrArg ResourcePool.ofList (splitInto_events refs path)

/-- Exactly one operation executes per requested native shift. -/
theorem shiftInto_eventCount (count : Nat) (work : CWriteRef ctx (.unsignedWord width))
    (path : (shiftInto (model := model) count work).Path) :
    ((shiftInto (model := model) count work).eventTrace path).length = count := by
  rw [shiftInto_events]
  exact List.length_replicate

/-- A complete actual split executes exactly the low width plus two native operations. -/
theorem splitInto_eventCount (refs : Refs ctx highWidth lowWidth)
    (path : (splitInto (model := model) refs).Path) :
    ((splitInto (model := model) refs).eventTrace path).length = lowWidth + 2 := by
  rw [splitInto_events]
  simp only [splitTrace, shiftTrace, List.length_append, List.length_replicate,
    List.length_singleton]
  omega

/-- The actual serial shift depth is the prescribed shift count at unit duration. -/
theorem shiftInto_depth (count : Nat) (work : CWriteRef ctx (.unsignedWord width))
    (path : (shiftInto (model := model) count work).Path) :
    (shiftInto (model := model) count work).depth (fun _ => 1) path = count := by
  change 0 + (∑ _index : Fin count, 1) = count
  simp

/-- Word-split dependencies have exact unit-duration depth equal to the low width plus two. -/
theorem splitInto_depth (refs : Refs ctx highWidth lowWidth)
    (path : (splitInto (model := model) refs).Path) :
    (splitInto (model := model) refs).depth (fun _ => 1) path = lowWidth + 2 := by
  change 1 + ((shiftInto (model := model) lowWidth refs.work).depth (fun _ => 1) path.2.1 + 1) = _
  rw [shiftInto_depth]
  omega

/-- All actual native shifts restore the complete borrowed-reference joint state. -/
theorem shiftInto_borrowedRestored (count : Nat) (work : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (shiftInto (model := model) count work).BorrowedRestored Reference state
      ((shiftInto (model := model) count work).execute Reference state) :=
  Circuit.borrowedRestored_iterate
    (BitWord.instruction (execution := model) (shiftOp work)) Reference
    (Circuit.borrowedRestored_classical (model := model)
      (BitWord.selectedApplication (execution := model) (shiftOp work))) count state

/-- The complete actual word split restores all borrowed correlations jointly with references. -/
theorem splitInto_borrowedRestored (refs : Refs ctx highWidth lowWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (splitInto (model := model) refs).BorrowedRestored Reference state
      ((splitInto (model := model) refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq
    (BitWord.instruction (execution := model) (lowOp refs)) (tailInto (model := model) refs)
  · exact Circuit.borrowedRestored_classical (model := model) _ state
  · exact Circuit.borrowedRestored_seq _ _ _
      (shiftInto_borrowedRestored lowWidth refs.work Reference _)
      (Circuit.borrowedRestored_classical (model := model) _ _)

/-- Every native shift and the iteration boundary use the complete supplied context. -/
theorem shiftInto_visited (count : Nat) (work : CWriteRef ctx (.unsignedWord width))
    (path : (shiftInto (model := model) count work).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (shiftInto (model := model) count work).visitedContexts path) :
    visited = ctx := by
  change visited ∈ ctx :: (List.ofFn (fun _index : Fin count => [ctx])).flatten at present
  have actual : visited = ctx ∨ count ≠ 0 ∧ visited = ctx := by simpa using present
  exact actual.elim id And.right

/-- Every actual word-split instruction uses only the complete supplied live context. -/
theorem splitInto_visited (refs : Refs ctx highWidth lowWidth)
    (path : (splitInto (model := model) refs).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (splitInto (model := model) refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ ([ctx] ++ (_ ++ [ctx])) at present
  simp only [List.mem_append, List.mem_singleton] at present
  rcases present with low | shift | high
  · exact low
  · exact shiftInto_visited lowWidth refs.work path.2.1 visited shift
  · exact high

/-- Every original resident resource remains counted throughout the actual split. -/
theorem splitInto_resident_le (refs : Refs ctx highWidth lowWidth)
    (path : (splitInto (model := model) refs).Path) :
    (splitInto (model := model) refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [splitInto_visited refs path visited present]

/-- Every original auxiliary role remains counted throughout the actual split. -/
theorem splitInto_auxiliary_le (refs : Refs ctx highWidth lowWidth)
    (path : (splitInto (model := model) refs).Path) :
    (splitInto (model := model) refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [splitInto_visited refs path visited present]

end

end QuantumAlg.ClassicalRoutines.Word.Split
