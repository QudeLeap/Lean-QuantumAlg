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

variable {width : Nat} {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Independent comparison and selected row-exchange instruction formula. -/
def branchTrace (width : Nat) (passes : Bool) : List (Resource.Event model) :=
  ClassicalRoutines.Comparison.Doubled.comparisonTrace (model := model) width ++
    if passes then [] else LatticeSwap.pointSwapTrace (model := model) width

private theorem select_events (refs : Refs ctx width)
    (path : (selectInto (model := model) refs).Path) :
    (selectInto (model := model) refs).eventTrace path =
      if path.1.toBool then [] else LatticeSwap.pointSwapTrace (model := model) width := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag =>
    cases flag
    · change (LatticeSwap.pointSwap (model := model)
        refs.basis.second refs.basis.third refs.swapScratch).eventTrace path =
          LatticeSwap.pointSwapTrace (model := model) width
      exact LatticeSwap.pointSwap_events _ _ _ path
    · rfl

/-- Every actual branch path emits the independent comparison and selected-exchange formula. -/
theorem branchInto_events (refs : Refs ctx width)
    (path : (branchInto (model := model) refs).Path) :
    (branchInto (model := model) refs).eventTrace path =
      branchTrace (model := model) width path.2.1.toBool := by
  change _ ++ _ = _
  rw [LatticeLovasz.secondLovaszInto_events, select_events]
  rfl

/-- Actual native multiplicity comes from that same independent branch formula. -/
theorem branchInto_resourcePool (refs : Refs ctx width)
    (path : (branchInto (model := model) refs).Path) :
    (branchInto (model := model) refs).resourcePool path =
      ResourcePool.ofList (branchTrace (model := model) width path.2.1.toBool) := by
  change ResourcePool.ofList ((branchInto (model := model) refs).eventTrace path) = _
  rw [branchInto_events]

private theorem select_count (refs : Refs ctx width)
    (path : (selectInto (model := model) refs).Path) :
    ((selectInto (model := model) refs).eventTrace path).length ≤ 9 := by
  rw [select_events]
  split <;> simp [LatticeSwap.pointSwapTrace]

/-- Every actual second-Lovasz path executes at most twelve native operations. -/
theorem branchInto_eventCount_le (refs : Refs ctx width)
    (path : (branchInto (model := model) refs).Path) :
    ((branchInto (model := model) refs).eventTrace path).length ≤ 12 := by
  have selected := select_count refs path.2
  change List.length (_ ++ _) ≤ 12
  simp only [List.length_append]
  change 3 + ((selectInto (model := model) refs).eventTrace path.2).length ≤ 12
  omega

private theorem select_depth (refs : Refs ctx width)
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

/-- Unit-duration depth includes the dependence of row exchange on the actual comparison bit. -/
theorem branchInto_depth_le (refs : Refs ctx width)
    (path : (branchInto (model := model) refs).Path) :
    (branchInto (model := model) refs).depth (fun _ => 1) path ≤ 12 := by
  have selected := select_depth refs path.2
  change 3 + (selectInto (model := model) refs).depth (fun _ => 1) path.2 ≤ 12
  omega

private theorem select_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (selectInto (model := model) refs).BorrowedRestored Reference state
      ((selectInto (model := model) refs).execute Reference state) := by
  apply Circuit.borrowedRestored_branch _ _ Reference _ state
  intro flag History _ state
  cases flag with
  | bit flag =>
    cases flag
    · exact LatticeSwap.pointSwap_borrowedRestored _ _ _ Reference state
    · exact Circuit.borrowedRestored_id (model := model) (ctx := ctx) state

/-- The actual comparison and selected arm restore all borrowed-reference correlations. -/
theorem branchInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (branchInto (model := model) refs).BorrowedRestored Reference state
      ((branchInto (model := model) refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (LatticeLovasz.secondLovaszInto_borrowedRestored refs.lovasz Reference state)
    (select_borrowedRestored refs Reference _)

private theorem select_visited (refs : Refs ctx width)
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

/-- The complete actual branch visits only the complete original supplied context. -/
theorem branchInto_visited (refs : Refs ctx width) (path : (branchInto (model := model) refs).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (branchInto (model := model) refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (_ ++ _) at present
  rcases List.mem_append.mp present with comparison | selected
  · change visited ∈ [ctx, ctx, ctx] at comparison
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using comparison
  · exact select_visited refs path.2 visited selected

/-- Resident space counts all original quantum dimensions and actual classical cells. -/
theorem branchInto_resident_le (refs : Refs ctx width)
    (path : (branchInto (model := model) refs).Path) :
    (branchInto (model := model) refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [branchInto_visited refs path visited present]

/-- Auxiliary space retains every original role and the exchange scratch throughout execution. -/
theorem branchInto_auxiliary_le (refs : Refs ctx width)
    (path : (branchInto (model := model) refs).Path) :
    (branchInto (model := model) refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [branchInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondLovaszBranch
