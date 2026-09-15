/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Row.Swap

/-!
# Actual row-swap resources

The complete execution counts nine native copies and retains the scratch word.
Full borrowed restoration is independent of any scratch-cleanliness promise.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSwap

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent native instruction formula for the complete original row exchange. -/
def pointSwapTrace (width : Nat) : List (Resource.Event kind) :=
  List.replicate 9 (.classicalOperation (.wordUnary .copy width))

/-- The actual row exchange emits exactly the nine independently specified copy operations. -/
theorem pointSwap_events (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width)) (path : (pointSwap left right scratch).Path) :
    (pointSwap left right scratch).eventTrace path = pointSwapTrace width := rfl

/-- Actual native multiplicity comes from the same independent nine-copy formula. -/
theorem pointSwap_resourcePool (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width)) (path : (pointSwap left right scratch).Path) :
    (pointSwap left right scratch).resourcePool path =
      ResourcePool.ofList (pointSwapTrace width) := rfl

/-- Actual serial depth is exactly nine at unit native instruction duration. -/
theorem pointSwap_depth (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width)) (path : (pointSwap left right scratch).Path) :
    (pointSwap left right scratch).depth (fun _ => 1) path = 9 := rfl

/-- One actual coordinate swap restores all borrowed-reference correlations. -/
theorem coordinateSwap_borrowedRestored (left right scratch : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (coordinateSwap left right scratch).BorrowedRestored Reference state
      ((coordinateSwap left right scratch).execute Reference state) := by
  refine Circuit.borrowedRestored_seq (.classical (LatticeRows.copyOp left scratch)) _ state
    (Circuit.borrowedRestored_classical _ state) ?_
  exact Circuit.borrowedRestored_seq _ _ _ (Circuit.borrowedRestored_classical _ _)
    (Circuit.borrowedRestored_classical _ _)

/-- Complete actual row swapping restores the full borrowed-reference joint state. -/
theorem pointSwap_borrowedRestored (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (pointSwap left right scratch).BorrowedRestored Reference state
      ((pointSwap left right scratch).execute Reference state) := by
  refine Circuit.borrowedRestored_seq (coordinateSwap left.first right.first scratch) _ state
    (coordinateSwap_borrowedRestored _ _ _ Reference state) ?_
  exact Circuit.borrowedRestored_seq _ _ _ (coordinateSwap_borrowedRestored _ _ _ Reference _)
    (coordinateSwap_borrowedRestored _ _ _ Reference _)

/-- Every actual copy visits the complete original context including scratch. -/
theorem pointSwap_visited (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width)) (path : (pointSwap left right scratch).Path) :
    (pointSwap left right scratch).visitedContexts path = List.replicate 9 ctx := rfl

/-- All supplied resident quantum and classical resources remain counted throughout swapping. -/
theorem pointSwap_resident_le (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width)) (path : (pointSwap left right scratch).Path) :
    (pointSwap left right scratch).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [pointSwap_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- Auxiliary roles and scratch residency remain counted throughout the actual exchange. -/
theorem pointSwap_auxiliary_le (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width)) (path : (pointSwap left right scratch).Path) :
    (pointSwap left right scratch).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [pointSwap_visited] at present
  rw [(List.mem_replicate.mp present).2]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSwap
