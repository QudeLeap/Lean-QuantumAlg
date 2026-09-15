/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit.Restoration

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Lovasz

/-!
# Actual second-Lovasz branch resources

Three comparison operations precede the actual selected identity or nine-copy
row exchange. The complete branch uses at most twelve native operations and
retains all supplied resources and borrowed correlations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondLovaszBranch

open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent comparison and selected row-exchange instruction formula. -/
def branchTrace (width : Nat) (passes : Bool) : List (Resource.Event kind) :=
  ClassicalRoutines.Comparison.Doubled.comparisonTrace width ++
    if passes then [] else LatticeSwap.pointSwapTrace width

private theorem select_events (refs : Refs ctx width) (path : (selectInto refs).Path) :
    (selectInto refs).eventTrace path =
      if path.1.toBool then [] else LatticeSwap.pointSwapTrace width := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag => cases flag <;> rfl

/-- Every actual branch path emits the independent comparison and selected-exchange formula. -/
theorem branchInto_events (refs : Refs ctx width) (path : (branchInto refs).Path) :
    (branchInto refs).eventTrace path = branchTrace width path.2.1.toBool := by
  change _ ++ _ = _
  rw [LatticeLovasz.secondLovaszInto_events, select_events]
  rfl

/-- Actual native multiplicity comes from that same independent branch formula. -/
theorem branchInto_resourcePool (refs : Refs ctx width) (path : (branchInto refs).Path) :
    (branchInto refs).resourcePool path =
      ResourcePool.ofList (branchTrace width path.2.1.toBool) := by
  change ResourcePool.ofList ((branchInto refs).eventTrace path) = _
  rw [branchInto_events]

private theorem select_count (refs : Refs ctx width) (path : (selectInto refs).Path) :
    ((selectInto refs).eventTrace path).length ≤ 9 := by
  rw [select_events]
  split <;> simp [LatticeSwap.pointSwapTrace]

/-- Every actual second-Lovasz path executes at most twelve native operations. -/
theorem branchInto_eventCount_le (refs : Refs ctx width) (path : (branchInto refs).Path) :
    ((branchInto refs).eventTrace path).length ≤ 12 := by
  have selected := select_count refs path.2
  change List.length (_ ++ _) ≤ 12
  simp only [List.length_append]
  change 3 + ((selectInto refs).eventTrace path.2).length ≤ 12
  omega

private theorem select_depth (refs : Refs ctx width) (path : (selectInto refs).Path) :
    (selectInto refs).depth (fun _ => 1) path ≤ 9 := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag =>
    cases flag
    · change 9 ≤ 9
      omega
    · change 0 ≤ 9
      omega

/-- Unit-duration depth includes the dependence of row exchange on the actual comparison bit. -/
theorem branchInto_depth_le (refs : Refs ctx width) (path : (branchInto refs).Path) :
    (branchInto refs).depth (fun _ => 1) path ≤ 12 := by
  have selected := select_depth refs path.2
  change 3 + (selectInto refs).depth (fun _ => 1) path.2 ≤ 12
  omega

private theorem select_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (selectInto refs).BorrowedRestored Reference state
      ((selectInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_branch _ _ Reference _ state
  intro flag History _ state
  cases flag with
  | bit flag =>
    cases flag
    · exact LatticeSwap.pointSwap_borrowedRestored _ _ _ Reference state
    · change (Circuit.id ctx).BorrowedRestored Reference state
        ((Circuit.id ctx).execute Reference state)
      rw [Circuit.BorrowedRestored, observeBorrowedAfter_sameContext, Circuit.execute_id]
      exact observeBorrowed_mapHistory state _

/-- The actual comparison and selected arm restore all borrowed-reference correlations. -/
theorem branchInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (branchInto refs).BorrowedRestored Reference state
      ((branchInto refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (LatticeLovasz.secondLovaszInto_borrowedRestored refs.lovasz Reference state)
    (select_borrowedRestored refs Reference _)

private theorem select_visited (refs : Refs ctx width) (path : (selectInto refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (selectInto refs).visitedContexts path) :
    visited = ctx := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag =>
    cases flag
    · change visited ∈ [ctx, ctx, ctx, ctx, ctx, ctx, ctx, ctx, ctx] at present
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present
    · change visited ∈ [ctx] at present
      exact List.mem_singleton.mp present

/-- The complete actual branch visits only the complete original supplied context. -/
theorem branchInto_visited (refs : Refs ctx width) (path : (branchInto refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (branchInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (_ ++ _) at present
  rcases List.mem_append.mp present with comparison | selected
  · change visited ∈ [ctx, ctx, ctx] at comparison
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using comparison
  · exact select_visited refs path.2 visited selected

/-- Resident space counts all original quantum dimensions and actual classical cells. -/
theorem branchInto_resident_le (refs : Refs ctx width) (path : (branchInto refs).Path) :
    (branchInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [branchInto_visited refs path visited present]

/-- Auxiliary space retains every original role and the exchange scratch throughout execution. -/
theorem branchInto_auxiliary_le (refs : Refs ctx width) (path : (branchInto refs).Path) :
    (branchInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [branchInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondLovaszBranch
