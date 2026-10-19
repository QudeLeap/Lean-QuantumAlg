/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Gram.Program

/-!
# Actual Gram refresh resources

Six native dot refreshes cost exactly thirty operations and unit-duration
serial depth thirty. All original classical and quantum resources remain live.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeMetricMachine

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent thirty-instruction formula for the six overwritten Gram outputs. -/
def gramTrace {model : ExecutionModel} [BitWord.Selected model] (width : Nat) :
    List (Resource.Event model) :=
  (List.replicate 6 [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .add width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .add width))]).flatten

/-- Every actual Gram path has exactly the independent thirty-instruction trace. -/
lemma refreshInto_events {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) basis refs).Path) :
    (refreshInto (model := model) basis refs).eventTrace path =
      gramTrace (model := model) width := by
  change _ ++ (_ ++ (_ ++ (_ ++ (_ ++ _)))) = _
  simp only [entryInto, LatticeDotRefresh.refreshInto_events]
  rfl

/-- Actual native multiplicities are those of the independent Gram instruction formula. -/
lemma refreshInto_resourcePool {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) basis refs).Path) :
    (refreshInto (model := model) basis refs).resourcePool path =
      ResourcePool.ofList (gramTrace (model := model) width) := by
  change ResourcePool.ofList ((refreshInto (model := model) basis refs).eventTrace path) = _
  rw [refreshInto_events]

/-- Exactly thirty native operations execute in the complete actual Gram refresh. -/
lemma refreshInto_eventCount {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) basis refs).Path) :
    ((refreshInto (model := model) basis refs).eventTrace path).length = 30 := by
  rw [refreshInto_events]
  rfl

/-- The actual serial dependency depth is thirty at unit instruction duration. -/
lemma refreshInto_depth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) basis refs).Path) :
    (refreshInto (model := model) basis refs).depth (fun _ => 1) path = 30 := rfl

/-- All six actual refreshes restore borrowed correlations jointly with external references. -/
lemma refreshInto_borrowedRestored {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (refreshInto (model := model) basis refs).BorrowedRestored Reference state
      ((refreshInto (model := model) basis refs).execute environment Reference state) := by
  refine Circuit.borrowedRestored_seq
    (environment := environment) (entryInto basis refs .g11) _ state
    (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _) ?_
  refine Circuit.borrowedRestored_seq (environment := environment) (entryInto basis refs .g21) _ _
    (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _) ?_
  refine Circuit.borrowedRestored_seq (environment := environment) (entryInto basis refs .g31) _ _
    (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _) ?_
  refine Circuit.borrowedRestored_seq (environment := environment) (entryInto basis refs .g22) _ _
    (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _) ?_
  refine Circuit.borrowedRestored_seq (environment := environment) (entryInto basis refs .g32) _ _
    (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _) ?_
  exact LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _

/-- All thirty actual instructions use the original complete context. -/
lemma refreshInto_visited {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) basis refs).Path) :
    (refreshInto (model := model) basis refs).visitedContexts path =
      List.replicate 30 ctx := rfl

/-- Resident accounting includes the complete supplied quantum and classical storage. -/
lemma refreshInto_resident_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) basis refs).Path) :
    (refreshInto (model := model) basis refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [refreshInto_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- Auxiliary accounting retains all original cell roles throughout the actual computation. -/
lemma refreshInto_auxiliary_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (path : (refreshInto (model := model) basis refs).Path) :
    (refreshInto (model := model) basis refs).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [refreshInto_visited] at present
  rw [(List.mem_replicate.mp present).2]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeMetricMachine
