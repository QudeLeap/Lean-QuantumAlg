/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Rounds.Program
import all QuantumAlg.Components.Classical.NumberTheory.IntegerSqrt.Resources

/-!
# Native resources of the actual finite refinement loop
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt

open Execution
open scoped BigOperators

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {inputWidth : Nat}

/-- The independent chronological instruction list of the finite refinement chain. -/
def roundsTrace (inputWidth remaining : Nat) : List (Resource.Event kind) :=
  (List.replicate remaining (IntegerSqrt.roundTrace (workWidth inputWidth))).flatten

/-- Each recorded branch vector emits the same original six-operation round sequence. -/
theorem roundsInto_events (refs : Refs ctx inputWidth) (remaining : Nat)
    (path : (roundsInto refs remaining).Path) :
    (roundsInto refs remaining).eventTrace path = roundsTrace inputWidth remaining := by
  simp only [roundsInto, Circuit.eventTrace, IntegerSqrt.roundInto_events,
    List.ofFn_const, roundsTrace]

private theorem roundsTrace_pool (inputWidth remaining : Nat) :
    ResourcePool.ofList (roundsTrace (kind := kind) inputWidth remaining) =
      ResourcePool.scale remaining
        (ResourcePool.ofList (IntegerSqrt.roundTrace (workWidth inputWidth))) := by
  induction remaining with
  | zero => rfl
  | succ remaining inductionHypothesis =>
      unfold roundsTrace at inductionHypothesis ⊢
      rw [List.replicate_succ, List.flatten_cons, ResourcePool.ofList_append,
        inductionHypothesis, ResourcePool.scale_succ]

/-- The actual loop has exactly the independently scaled original native coordinates. -/
theorem roundsInto_resourcePool (refs : Refs ctx inputWidth) (remaining : Nat)
    (path : (roundsInto refs remaining).Path) :
    (roundsInto refs remaining).resourcePool path = ResourcePool.scale remaining
      (ResourcePool.ofList (IntegerSqrt.roundTrace (workWidth inputWidth))) := by
  change ResourcePool.ofList ((roundsInto refs remaining).eventTrace path) = _
  rw [roundsInto_events, roundsTrace_pool]

/-- Six dependent native instructions are charged for every actual refinement round. -/
theorem roundsInto_eventCount (refs : Refs ctx inputWidth) (remaining : Nat)
    (path : (roundsInto refs remaining).Path) :
    ((roundsInto refs remaining).eventTrace path).length = remaining * 6 := by
  rw [roundsInto_events]
  simp [roundsTrace, IntegerSqrt.roundTrace]

/-- The actual iteration retains the dependency between all six instructions of every round. -/
theorem roundsInto_depth (refs : Refs ctx inputWidth) (remaining : Nat)
    (path : (roundsInto refs remaining).Path) :
    (roundsInto refs remaining).depth (fun _ => 1) path = remaining * 6 := by
  change (DepthExpr.depthEval (fun _ => 1)
    (.indexedProduct "circuit-iteration" remaining .id
      (fun index => (IntegerSqrt.roundInto (wideInput refs) refs.round).eventDepth
        (path index)))) = _
  change 0 + (∑ index : Fin remaining,
    (IntegerSqrt.roundInto (wideInput refs) refs.round).depth (fun _ => 1) (path index)) = _
  simp [IntegerSqrt.roundInto_depth]

/-- The original context is the only context visited by the finite refinement loop. -/
theorem roundsInto_visited (refs : Refs ctx inputWidth) (remaining : Nat)
    (path : (roundsInto refs remaining).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (roundsInto refs remaining).visitedContexts path) : visited = ctx := by
  change visited ∈ ctx :: (List.ofFn (fun index : Fin remaining =>
    (IntegerSqrt.roundInto (wideInput refs) refs.round).visitedContexts (path index))).flatten
    at present
  rcases List.mem_cons.mp present with same | bodyPresent
  · exact same
  · obtain ⟨contexts, contextMember, visitedMember⟩ := List.mem_flatten.mp bodyPresent
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp contextMember
    simpa only [IntegerSqrt.roundInto_visited, List.mem_cons, List.not_mem_nil,
      or_false, or_self] using visitedMember

/-- Every actual loop path retains all original resident storage. -/
theorem roundsInto_resident_le (refs : Refs ctx inputWidth) (remaining : Nat)
    (path : (roundsInto refs remaining).Path) :
    (roundsInto refs remaining).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [roundsInto_visited refs remaining path visited present]

/-- Every actual loop path retains the original auxiliary roles. -/
theorem roundsInto_auxiliary_le (refs : Refs ctx inputWidth) (remaining : Nat)
    (path : (roundsInto refs remaining).Path) :
    (roundsInto refs remaining).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [roundsInto_visited refs remaining path visited present]

/-- Iterating actual rounds restores the complete borrowed state and external correlations. -/
theorem roundsInto_borrowedRestored (refs : Refs ctx inputWidth) (remaining : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (roundsInto refs remaining).BorrowedRestored Reference state
      ((roundsInto refs remaining).execute Reference state) :=
  Circuit.borrowedRestored_iterate (IntegerSqrt.roundInto (wideInput refs) refs.round) Reference
    (IntegerSqrt.roundInto_borrowedRestored (wideInput refs) refs.round Reference) remaining state

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt
