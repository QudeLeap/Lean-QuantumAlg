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

/-- Independent selected row-reduction and norm-refresh instructions. -/
def reductionTrace {model : ExecutionModel} [BitWord.Selected model] (width : Nat) :
    List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .sub width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .sub width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .sub width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .add width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .add width))]

/-- Independent complete formula for the four recorded branch decisions. -/
def firstPairTrace {model : ExecutionModel} [BitWord.Selected model] (width : Nat)
    (magnitudeNegative correctionNegative restoreNegative passes : Bool) :
    List (Resource.Event model) :=
  (RoundedDiv.bodyTrace (model := model) width magnitudeNegative correctionNegative
      restoreNegative ++ reductionTrace (model := model) width) ++
    (ClassicalRoutines.Comparison.Doubled.comparisonTrace (model := model) width ++
      if passes then [] else LatticeSwap.pointSwapTrace (model := model) width)

private lemma select_events {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width)
    (path : (selectInto (model := model) refs).Path) :
    (selectInto (model := model) refs).eventTrace path =
      if path.1.toBool then [] else LatticeSwap.pointSwapTrace (model := model) width := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag =>
    cases flag
    · change (LatticeSwap.pointSwap (model := model)
        refs.basis.first refs.basis.second refs.swapScratch).eventTrace path =
          LatticeSwap.pointSwapTrace (model := model) width
      exact LatticeSwap.pointSwap_events _ _ _ path
    · rfl

/-- Every actual path emits exactly the independently specified native instruction sequence. -/
lemma firstPairInto_events {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width)
    (path : (firstPairInto (model := model) refs).Path) :
    (firstPairInto (model := model) refs).eventTrace path =
      firstPairTrace (model := model) width
      path.1.1.1.1.2.1.toBool path.1.1.2.1.2.1.1.toBool path.1.1.2.2.2.2.1.toBool
      path.2.2.1.toBool := by
  change (_ ++ (_ ++ _)) ++ (_ ++ _) = _
  rw [RoundedDiv.body_events, LatticeArithmetic.pointReduce_events,
    LatticeNormRefresh.refreshInto_events, LatticeLovasz.firstLovaszInto_events, select_events]
  rfl

/-- Actual native multiplicity is counted from that same independent instruction formula. -/
lemma firstPairInto_resourcePool {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width)
    (path : (firstPairInto (model := model) refs).Path) :
    (firstPairInto (model := model) refs).resourcePool path =
      ResourcePool.ofList (firstPairTrace (model := model) width
      path.1.1.1.1.2.1.toBool path.1.1.2.1.2.1.1.toBool path.1.1.2.2.2.2.1.toBool
      path.2.2.1.toBool) := by
  change ResourcePool.ofList ((firstPairInto (model := model) refs).eventTrace path) = _
  rw [firstPairInto_events]

private lemma select_count {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width)
    (path : (selectInto (model := model) refs).Path) :
    ((selectInto (model := model) refs).eventTrace path).length ≤ 9 := by
  rw [select_events]
  split <;> simp [LatticeSwap.pointSwapTrace]

/-- At most 36 actual native instructions execute, including a failed-test row exchange. -/
lemma firstPairInto_eventCount_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width)
    (path : (firstPairInto (model := model) refs).Path) :
    ((firstPairInto (model := model) refs).eventTrace path).length ≤ 36 := by
  have division := RoundedDiv.body_eventCount_le refs.division path.1.1
  have selected := select_count refs path.2.2
  change List.length ((_ ++ (_ ++ _)) ++ (_ ++ _)) ≤ 36
  simp only [List.length_append]
  change ((RoundedDiv.body (model := model) refs.division).eventTrace path.1.1).length +
    (6 + 5) + (3 + ((selectInto (model := model) refs).eventTrace path.2.2).length) ≤ 36
  omega

private lemma select_depth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width)
    (path : (selectInto (model := model) refs).Path) :
    (selectInto (model := model) refs).depth (fun _ => 1) path ≤ 9 := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag =>
    cases flag
    · change 9 ≤ 9
      omega
    · change 0 ≤ 9
      omega

/-- Unit-duration serial depth retains all dependencies and is at most 36. -/
lemma firstPairInto_depth_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width)
    (path : (firstPairInto (model := model) refs).Path) :
    (firstPairInto (model := model) refs).depth (fun _ => 1) path ≤ 36 := by
  have division := RoundedDiv.body_depth_le refs.division path.1.1
  have selected := select_depth refs path.2.2
  change (RoundedDiv.body (model := model) refs.division).depth (fun _ => 1) path.1.1 +
    (6 + 5) + (3 + (selectInto (model := model) refs).depth (fun _ => 1) path.2.2) ≤ 36
  omega

private lemma select_borrowedRestored {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (selectInto (model := model) refs).BorrowedRestored Reference state
      ((selectInto (model := model) refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_branch (environment := environment) _ _ Reference _ state
  intro flag History _ state
  cases flag with
  | bit flag =>
    cases flag
    · exact LatticeSwap.pointSwap_borrowedRestored _ _ _ Reference state
    · exact Circuit.borrowedRestored_id
        (environment := environment) (model := model) (ctx := ctx) state

/-- Complete actual execution restores borrowed correlations jointly with external references. -/
lemma firstPairInto_borrowedRestored {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (firstPairInto (model := model) refs).BorrowedRestored Reference state
      ((firstPairInto (model := model) refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_seq (environment := environment)
    (reductionPrefixInto (model := model) refs) (lovaszBranchInto (model := model) refs)
  · apply Circuit.borrowedRestored_seq (environment := environment)
      (RoundedDiv.body (model := model) refs.division) (reduceRefreshInto (model := model) refs)
    · exact RoundedDiv.body_borrowedRestored refs.division Reference state
    · exact Circuit.borrowedRestored_seq (environment := environment) _ _ _
        (LatticeArithmetic.pointReduce_borrowedRestored _ _ _ _ Reference _)
        (LatticeNormRefresh.refreshInto_borrowedRestored _ _ Reference _)
  · exact Circuit.borrowedRestored_seq (environment := environment) _ _ _
      (LatticeLovasz.firstLovaszInto_borrowedRestored _ _ Reference _)
      (select_borrowedRestored refs Reference _)

private lemma select_visited {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width)
    (path : (selectInto (model := model) refs).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (selectInto (model := model) refs).visitedContexts path) :
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
lemma firstPairInto_visited {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width)
    (path : (firstPairInto (model := model) refs).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (firstPairInto (model := model) refs).visitedContexts path) :
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
lemma firstPairInto_resident_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width)
    (path : (firstPairInto (model := model) refs).Path) :
    (firstPairInto (model := model) refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [firstPairInto_visited refs path visited present]

/-- Auxiliary accounting retains the original roles and counts scratch throughout execution. -/
lemma firstPairInto_auxiliary_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width)
    (path : (firstPairInto (model := model) refs).Path) :
    (firstPairInto (model := model) refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [firstPairInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFirstPairMachine
