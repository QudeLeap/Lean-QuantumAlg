/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Restoration

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FirstPair.Program

/-!
# Actual first-pair resources

The chronological native instruction formula includes the actual division and
Lovasz selections. Every path uses at most 36 operations, with no allocation.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFirstPairMachine

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent native row-reduction and norm-refresh instructions. -/
def reductionTrace (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordBinary .mulLow width), .classicalOperation (.wordBinary .sub width),
    .classicalOperation (.wordBinary .mulLow width), .classicalOperation (.wordBinary .sub width),
    .classicalOperation (.wordBinary .mulLow width), .classicalOperation (.wordBinary .sub width),
    .classicalOperation (.wordBinary .mulLow width),
    .classicalOperation (.wordBinary .mulLow width), .classicalOperation (.wordBinary .add width),
    .classicalOperation (.wordBinary .mulLow width), .classicalOperation (.wordBinary .add width)]

/-- Independent complete formula for the four recorded branch decisions. -/
def firstPairTrace (width : Nat)
    (magnitudeNegative correctionNegative restoreNegative passes : Bool) :
    List (Resource.Event kind) :=
  (RoundedDiv.bodyTrace width magnitudeNegative correctionNegative restoreNegative ++
    reductionTrace width) ++ (ClassicalRoutines.Comparison.Doubled.comparisonTrace width ++
      if passes then [] else LatticeSwap.pointSwapTrace width)

private theorem select_events (refs : Refs ctx width) (path : (selectInto refs).Path) :
    (selectInto refs).eventTrace path =
      if path.1.toBool then [] else LatticeSwap.pointSwapTrace width := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag => cases flag <;> rfl

/-- Every actual path emits exactly the independently specified native instruction sequence. -/
theorem firstPairInto_events (refs : Refs ctx width) (path : (firstPairInto refs).Path) :
    (firstPairInto refs).eventTrace path = firstPairTrace width
      path.1.1.1.1.2.1.toBool path.1.1.2.1.2.1.1.toBool path.1.1.2.2.2.2.1.toBool
      path.2.2.1.toBool := by
  change (_ ++ (_ ++ _)) ++ (_ ++ _) = _
  rw [RoundedDiv.body_events, LatticeArithmetic.pointReduce_events,
    LatticeNormRefresh.refreshInto_events, LatticeLovasz.firstLovaszInto_events, select_events]
  rfl

/-- Actual native multiplicity is counted from that same independent instruction formula. -/
theorem firstPairInto_resourcePool (refs : Refs ctx width) (path : (firstPairInto refs).Path) :
    (firstPairInto refs).resourcePool path = ResourcePool.ofList (firstPairTrace width
      path.1.1.1.1.2.1.toBool path.1.1.2.1.2.1.1.toBool path.1.1.2.2.2.2.1.toBool
      path.2.2.1.toBool) := by
  change ResourcePool.ofList ((firstPairInto refs).eventTrace path) = _
  rw [firstPairInto_events]

private theorem select_count (refs : Refs ctx width) (path : (selectInto refs).Path) :
    ((selectInto refs).eventTrace path).length ≤ 9 := by
  rw [select_events]
  split <;> simp [LatticeSwap.pointSwapTrace]

/-- At most 36 actual native instructions execute, including a failed-test row exchange. -/
theorem firstPairInto_eventCount_le (refs : Refs ctx width) (path : (firstPairInto refs).Path) :
    ((firstPairInto refs).eventTrace path).length ≤ 36 := by
  have division := RoundedDiv.body_eventCount_le refs.division path.1.1
  have selected := select_count refs path.2.2
  change List.length ((_ ++ (_ ++ _)) ++ (_ ++ _)) ≤ 36
  simp only [List.length_append]
  change ((RoundedDiv.body refs.division).eventTrace path.1.1).length + (6 + 5) +
    (3 + ((selectInto refs).eventTrace path.2.2).length) ≤ 36
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

/-- Unit-duration serial depth retains all dependencies and is at most 36. -/
theorem firstPairInto_depth_le (refs : Refs ctx width) (path : (firstPairInto refs).Path) :
    (firstPairInto refs).depth (fun _ => 1) path ≤ 36 := by
  have division := RoundedDiv.body_depth_le refs.division path.1.1
  have selected := select_depth refs path.2.2
  change (RoundedDiv.body refs.division).depth (fun _ => 1) path.1.1 + (6 + 5) +
    (3 + (selectInto refs).depth (fun _ => 1) path.2.2) ≤ 36
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

/-- Complete actual execution restores borrowed correlations jointly with external references. -/
theorem firstPairInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (firstPairInto refs).BorrowedRestored Reference state
      ((firstPairInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq (reductionPrefixInto refs) (lovaszBranchInto refs)
  · apply Circuit.borrowedRestored_seq (RoundedDiv.body refs.division) (reduceRefreshInto refs)
    · exact RoundedDiv.body_borrowedRestored refs.division Reference state
    · exact Circuit.borrowedRestored_seq _ _ _
        (LatticeArithmetic.pointReduce_borrowedRestored _ _ _ _ Reference _)
        (LatticeNormRefresh.refreshInto_borrowedRestored _ _ Reference _)
  · exact Circuit.borrowedRestored_seq _ _ _
      (LatticeLovasz.firstLovaszInto_borrowedRestored _ _ Reference _)
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

/-- Every actual phase retains the complete supplied live context. -/
theorem firstPairInto_visited (refs : Refs ctx width) (path : (firstPairInto refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (firstPairInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ ((_ ++ (_ ++ _)) ++ (_ ++ _)) at present
  simp only [List.mem_append] at present
  rcases present with (division | reduction | refresh) | comparison | selected
  · exact RoundedDiv.body_visited refs.division path.1.1 visited division
  · rw [LatticeArithmetic.pointReduce_visited] at reduction
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using reduction
  · rw [LatticeNormRefresh.refreshInto_visited] at refresh
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using refresh
  · change visited ∈ [ctx, ctx, ctx] at comparison
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using comparison
  · exact select_visited refs path.2.2 visited selected

/-- Resident accounting includes all supplied classical cells and quantum systems. -/
theorem firstPairInto_resident_le (refs : Refs ctx width) (path : (firstPairInto refs).Path) :
    (firstPairInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [firstPairInto_visited refs path visited present]

/-- Auxiliary accounting retains the original roles and counts scratch throughout execution. -/
theorem firstPairInto_auxiliary_le (refs : Refs ctx width) (path : (firstPairInto refs).Path) :
    (firstPairInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [firstPairInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFirstPairMachine
