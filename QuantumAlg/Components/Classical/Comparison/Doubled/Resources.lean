/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Comparison.Doubled

/-!
# Actual doubled-comparison resources

The native trace counts the shift, comparison and complement in actual order.
Every resource remains live, and all borrowed-reference correlations survive.
-/

namespace QuantumAlg.ClassicalRoutines.Comparison.Doubled

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent native instruction formula for comparison with a doubled word. -/
def comparisonTrace (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordUnary .shiftLeft width),
    .classicalOperation (.wordBinary .lessThan width), .classicalOperation (.bit .not)]

/-- Actual comparison events match the independent three-operation formula. -/
theorem compareInto_events (refs : Refs ctx width) (path : (compareInto refs).Path) :
    (compareInto refs).eventTrace path = comparisonTrace width := rfl

/-- Actual native multiplicities come from the same independent three-operation formula. -/
theorem compareInto_resourcePool (refs : Refs ctx width) (path : (compareInto refs).Path) :
    (compareInto refs).resourcePool path = ResourcePool.ofList (comparisonTrace width) := rfl

/-- Actual serial depth includes the data dependence between all three operations. -/
theorem compareInto_depth (refs : Refs ctx width) (path : (compareInto refs).Path) :
    (compareInto refs).depth (fun _ => 1) path = 3 := rfl

/-- The actual comparison restores the complete borrowed-reference joint state. -/
theorem compareInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (compareInto refs).BorrowedRestored Reference state
      ((compareInto refs).execute Reference state) := by
  refine Circuit.borrowedRestored_seq (.classical (doubleOp refs)) _ state
    (Circuit.borrowedRestored_classical _ state) ?_
  exact Circuit.borrowedRestored_seq _ _ _ (Circuit.borrowedRestored_classical _ _)
    (Circuit.borrowedRestored_classical _ _)

/-- All three actual instructions use the complete original context. -/
theorem compareInto_visited (refs : Refs ctx width) (path : (compareInto refs).Path) :
    (compareInto refs).visitedContexts path = List.replicate 3 ctx := rfl

/-- Resident accounting retains all caller-supplied quantum and classical resources. -/
theorem compareInto_resident_le (refs : Refs ctx width) (path : (compareInto refs).Path) :
    (compareInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [compareInto_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- Auxiliary roles are preserved and counted throughout the actual comparison. -/
theorem compareInto_auxiliary_le (refs : Refs ctx width) (path : (compareInto refs).Path) :
    (compareInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [compareInto_visited] at present
  rw [(List.mem_replicate.mp present).2]

end

end QuantumAlg.ClassicalRoutines.Comparison.Doubled
