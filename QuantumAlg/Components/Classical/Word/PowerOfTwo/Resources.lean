/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Word.PowerOfTwo
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Actual native constant-loading resources

The independent formula has self-XOR, increment and the prescribed number of
one-bit left shifts. Count and serial unit-duration depth are exactly the
exponent plus two, with no additional live cell and complete borrowed recovery.
-/

namespace QuantumAlg.ClassicalRoutines.Word.PowerOfTwo

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent ordered formula for the requested native one-bit left shifts. -/
def shiftTrace (width count : Nat) : List (Resource.Event kind) :=
  List.replicate count (.classicalOperation (.wordUnary .shiftLeft width))

/-- Independent complete native formula for initializing and loading the prescribed power. -/
def powerTrace (width count : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordBinary .bitXor width),
    .classicalOperation (.wordUnary .increment width)] ++ shiftTrace width count

/-- Every actual repeated-shift path emits the exact independent native formula. -/
theorem shiftInto_events (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (path : (shiftInto count output).Path) :
    (shiftInto count output).eventTrace path = shiftTrace width count := by
  change (List.ofFn (fun _index : Fin count =>
    ([.classicalOperation (.wordUnary .shiftLeft width)] : List (Resource.Event kind)))).flatten = _
  simp [shiftTrace]

/-- Every actual constant-loading path emits its complete independent native formula. -/
theorem into_events (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (path : (into count output).Path) :
    (into count output).eventTrace path = powerTrace width count := by
  exact congrArg₂ List.append rfl (shiftInto_events count output path.2)

/-- Actual constant-loading multiplicities equal the complete independent native formula. -/
theorem into_resourcePool (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (path : (into count output).Path) :
    (into count output).resourcePool path = ResourcePool.ofList (powerTrace width count) :=
  congrArg ResourcePool.ofList (into_events count output path)

/-- The actual loader uses exactly one operation per shift plus both initialization operations. -/
theorem into_eventCount (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (path : (into count output).Path) :
    ((into count output).eventTrace path).length = count + 2 := by
  rw [into_events]
  simp only [powerTrace, shiftTrace, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

/-- Actual native left shifts have exactly the requested serial unit-duration depth. -/
theorem shiftInto_depth (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (path : (shiftInto count output).Path) :
    (shiftInto count output).depth (fun _ => 1) path = count := by
  change 0 + (∑ _index : Fin count, 1) = count
  simp

/-- Initialization precedes all actual native shifts in the exact dependency depth. -/
theorem into_depth (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (path : (into count output).Path) :
    (into count output).depth (fun _ => 1) path = count + 2 := by
  change (1 + 1) + (shiftInto count output).depth (fun _ => 1) path.2 = _
  rw [shiftInto_depth]
  omega

/-- Every actual repeated-shift path retains the complete supplied live context. -/
theorem shiftInto_visited (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (path : (shiftInto count output).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (shiftInto count output).visitedContexts path) : visited = ctx := by
  change visited ∈ ctx :: (List.ofFn (fun _index : Fin count => [ctx])).flatten at present
  have actual : visited = ctx ∨ count ≠ 0 ∧ visited = ctx := by simpa using present
  exact actual.elim id And.right

/-- Initialization and every native shift use only the complete original context. -/
theorem into_visited (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (path : (into count output).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (into count output).visitedContexts path) : visited = ctx := by
  change visited ∈ ([ctx] ++ [ctx]) ++ (shiftInto count output).visitedContexts path.2 at present
  simp only [List.mem_append, List.mem_singleton, or_self] at present
  exact present.elim id (shiftInto_visited count output path.2 visited)

/-- Every actual native shift restores borrowed storage jointly with all external references. -/
theorem shiftInto_borrowedRestored (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (shiftInto count output).BorrowedRestored Reference state
      ((shiftInto count output).execute Reference state) :=
  Circuit.borrowedRestored_iterate (.classical (shiftOp output)) Reference
    (Circuit.borrowedRestored_classical (shiftOp output)) count state

/-- The complete actual constant loader restores all borrowed-reference correlations jointly. -/
theorem into_borrowedRestored (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (into count output).BorrowedRestored Reference state
      ((into count output).execute Reference state) := by
  apply Circuit.borrowedRestored_seq (seedInto output) (shiftInto count output)
  · exact Circuit.borrowedRestored_seq (.classical (clearOp output))
      (.classical (incrementOp output)) state
      (Circuit.borrowedRestored_classical _ _) (Circuit.borrowedRestored_classical _ _)
  · exact shiftInto_borrowedRestored count output Reference _

/-- All original resident entries remain counted throughout the actual constant loader. -/
theorem into_resident_le (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (path : (into count output).Path) :
    (into count output).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited count output path visited present]

/-- All original auxiliary roles remain counted throughout the actual constant loader. -/
theorem into_auxiliary_le (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (path : (into count output).Path) :
    (into count output).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited count output path visited present]

end

end QuantumAlg.ClassicalRoutines.Word.PowerOfTwo
