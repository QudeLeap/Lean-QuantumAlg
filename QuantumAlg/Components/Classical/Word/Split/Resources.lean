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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width highWidth lowWidth : Nat}

/-- Independent native formula for the prescribed number of one-bit shifts. -/
def shiftTrace (width count : Nat) : List (Resource.Event kind) :=
  List.replicate count (.classicalOperation (.wordUnary .shiftRight width))

/-- Independent low-resize, native shifts, high-resize formula. -/
def splitTrace (highWidth lowWidth : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordResize (highWidth + lowWidth) lowWidth)] ++
    (shiftTrace (highWidth + lowWidth) lowWidth ++
      [.classicalOperation (.wordResize (highWidth + lowWidth) highWidth)])

/-- Every actual shift path emits exactly the independent replicated native instruction. -/
theorem shiftInto_events (count : Nat) (work : CWriteRef ctx (.unsignedWord width))
    (path : (shiftInto count work).Path) :
    (shiftInto count work).eventTrace path = shiftTrace width count := by
  change (List.ofFn (fun _index : Fin count =>
    ([.classicalOperation (.wordUnary .shiftRight width)] :
      List (Resource.Event kind)))).flatten = _
  simp [shiftTrace]

/-- Every actual word-split path emits the independent complete native formula. -/
theorem splitInto_events (refs : Refs ctx highWidth lowWidth) (path : (splitInto refs).Path) :
    (splitInto refs).eventTrace path = splitTrace highWidth lowWidth := by
  change _ ++ (_ ++ _) = _
  rw [shiftInto_events]
  rfl

/-- Actual native multiplicities equal the independent complete word-split formula. -/
theorem splitInto_resourcePool (refs : Refs ctx highWidth lowWidth)
    (path : (splitInto refs).Path) :
    (splitInto refs).resourcePool path = ResourcePool.ofList (splitTrace highWidth lowWidth) :=
  congrArg ResourcePool.ofList (splitInto_events refs path)

/-- Exactly one operation executes per requested native shift. -/
theorem shiftInto_eventCount (count : Nat) (work : CWriteRef ctx (.unsignedWord width))
    (path : (shiftInto count work).Path) :
    ((shiftInto count work).eventTrace path).length = count := by
  rw [shiftInto_events]
  exact List.length_replicate

/-- A complete actual split executes exactly the low width plus two native operations. -/
theorem splitInto_eventCount (refs : Refs ctx highWidth lowWidth) (path : (splitInto refs).Path) :
    ((splitInto refs).eventTrace path).length = lowWidth + 2 := by
  rw [splitInto_events]
  simp only [splitTrace, shiftTrace, List.length_append, List.length_replicate,
    List.length_singleton]
  omega

/-- The actual serial shift depth is the prescribed shift count at unit duration. -/
theorem shiftInto_depth (count : Nat) (work : CWriteRef ctx (.unsignedWord width))
    (path : (shiftInto count work).Path) :
    (shiftInto count work).depth (fun _ => 1) path = count := by
  change 0 + (∑ _index : Fin count, 1) = count
  simp

/-- Word-split dependencies have exact unit-duration depth equal to the low width plus two. -/
theorem splitInto_depth (refs : Refs ctx highWidth lowWidth) (path : (splitInto refs).Path) :
    (splitInto refs).depth (fun _ => 1) path = lowWidth + 2 := by
  change 1 + ((shiftInto lowWidth refs.work).depth (fun _ => 1) path.2.1 + 1) = _
  rw [shiftInto_depth]
  omega

/-- All actual native shifts restore the complete borrowed-reference joint state. -/
theorem shiftInto_borrowedRestored (count : Nat) (work : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (shiftInto count work).BorrowedRestored Reference state
      ((shiftInto count work).execute Reference state) :=
  Circuit.borrowedRestored_iterate (.classical (shiftOp work)) Reference
    (Circuit.borrowedRestored_classical (shiftOp work)) count state

/-- The complete actual word split restores all borrowed correlations jointly with references. -/
theorem splitInto_borrowedRestored (refs : Refs ctx highWidth lowWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (splitInto refs).BorrowedRestored Reference state
      ((splitInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq (.classical (lowOp refs)) (tailInto refs)
  · exact Circuit.borrowedRestored_classical _ state
  · exact Circuit.borrowedRestored_seq _ _ _
      (shiftInto_borrowedRestored lowWidth refs.work Reference _)
      (Circuit.borrowedRestored_classical _ _)

/-- Every native shift and the iteration boundary use the complete supplied context. -/
theorem shiftInto_visited (count : Nat) (work : CWriteRef ctx (.unsignedWord width))
    (path : (shiftInto count work).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (shiftInto count work).visitedContexts path) : visited = ctx := by
  change visited ∈ ctx :: (List.ofFn (fun _index : Fin count => [ctx])).flatten at present
  have actual : visited = ctx ∨ count ≠ 0 ∧ visited = ctx := by simpa using present
  exact actual.elim id And.right

/-- Every actual word-split instruction uses only the complete supplied live context. -/
theorem splitInto_visited (refs : Refs ctx highWidth lowWidth) (path : (splitInto refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (splitInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ ([ctx] ++ (_ ++ [ctx])) at present
  simp only [List.mem_append, List.mem_singleton] at present
  rcases present with low | shift | high
  · exact low
  · exact shiftInto_visited lowWidth refs.work path.2.1 visited shift
  · exact high

/-- Every original resident resource remains counted throughout the actual split. -/
theorem splitInto_resident_le (refs : Refs ctx highWidth lowWidth) (path : (splitInto refs).Path) :
    (splitInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [splitInto_visited refs path visited present]

/-- Every original auxiliary role remains counted throughout the actual split. -/
theorem splitInto_auxiliary_le (refs : Refs ctx highWidth lowWidth) (path : (splitInto refs).Path) :
    (splitInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [splitInto_visited refs path visited present]

end

end QuantumAlg.ClassicalRoutines.Word.Split
