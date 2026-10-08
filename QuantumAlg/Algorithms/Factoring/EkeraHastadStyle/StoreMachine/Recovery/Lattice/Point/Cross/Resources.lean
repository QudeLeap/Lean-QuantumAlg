/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Cross

/-!
# Actual cross-product resources and borrowed restoration

Six multiplications and three subtractions reuse the original caller context.
Borrowed restoration includes arbitrary external references.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCross

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {width : Nat} {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The complete actual cross product preserves every borrowed correlation. -/
theorem pointCrossInto_borrowedRestored (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (pointCrossInto (model := model) left right output productLeft productRight).BorrowedRestored
      Reference state
      ((pointCrossInto (model := model) left right output productLeft productRight).execute
        Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact coordinateCross_borrowedRestored _ _ _ _ _ _ _ Reference state
  · exact Circuit.borrowedRestored_seq _ _ _
      (coordinateCross_borrowedRestored _ _ _ _ _ _ _ Reference _)
      (coordinateCross_borrowedRestored _ _ _ _ _ _ _ Reference _)

/-- Every actual path has the same explicit nine native instructions. -/
theorem pointCrossInto_events (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width))
    (path : (pointCrossInto (model := model) left right output productLeft productRight).Path) :
    (pointCrossInto (model := model) left right output productLeft productRight).eventTrace path =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .sub width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .sub width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .mulLow width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .sub width))] := by
  unfold pointCrossInto coordinateCross at path
  unfold pointCrossInto coordinateCross
  change _ ++ (_ ++ _) = _
  rw [ProductDifference.computeInto_events, ProductDifference.computeInto_events,
    ProductDifference.computeInto_events]
  rfl

/-- All nine native instructions contribute their unit duration in the actual dependency order. -/
theorem pointCrossInto_depth (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width))
    (path : (pointCrossInto (model := model) left right output productLeft productRight).Path) :
    (pointCrossInto (model := model) left right output productLeft productRight).depth
      (fun _ => 1) path = 9 := rfl

/-- Every actual instruction uses the original caller context. -/
theorem pointCrossInto_visited (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width))
    (path : (pointCrossInto (model := model) left right output productLeft productRight).Path) :
    (pointCrossInto (model := model) left right output productLeft productRight).visitedContexts
      path =
      [ctx, ctx, ctx, ctx, ctx, ctx, ctx, ctx, ctx] := rfl

/-- Resident space counts all original classical cells and quantum systems. -/
theorem pointCrossInto_resident_le (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width))
    (path : (pointCrossInto (model := model) left right output productLeft productRight).Path) :
    (pointCrossInto (model := model) left right output productLeft productRight).peakResidentSpace
      path ≤
      ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [pointCrossInto_visited] at present
  have same : visited = ctx := by simpa only [List.mem_cons, List.not_mem_nil,
    or_false, or_self] using present
  rw [same]

/-- Auxiliary roles remain those of the caller's supplied storage. -/
theorem pointCrossInto_auxiliary_le (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width))
    (path : (pointCrossInto (model := model) left right output productLeft productRight).Path) :
    (pointCrossInto (model := model) left right output productLeft productRight).peakAuxiliarySpace
      path ≤
      ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [pointCrossInto_visited] at present
  have same : visited = ctx := by simpa only [List.mem_cons, List.not_mem_nil,
    or_false, or_self] using present
  rw [same]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCross
