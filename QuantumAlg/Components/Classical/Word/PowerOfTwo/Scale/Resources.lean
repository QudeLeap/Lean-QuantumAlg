/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Word.PowerOfTwo.Scale

/-!
# Actual native power-scaling resources

One source-width resize precedes the prescribed destination-width left shifts.
The independent native formula yields the exact count and unit-duration depth,
while all original context entries and borrowed correlations remain accounted.
-/

namespace QuantumAlg.ClassicalRoutines.Word.PowerOfTwo.Scale

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {sourceWidth width : Nat}

/-- Independent native resize and prescribed left-shift formula for actual word scaling. -/
def scaleTrace (sourceWidth width count : Nat) : List (Resource.Event model) :=
  [.classicalOperation
      (BitWord.selectedCoordinate (execution := model) (.wordResize sourceWidth width))] ++
    PowerOfTwo.shiftTrace (model := model) width count

/-- Every actual native scaling path emits the exact independent operation formula. -/
theorem into_events (count : Nat) (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (into (model := model) count input output).Path) :
    (into (model := model) count input output).eventTrace path =
      scaleTrace (model := model) sourceWidth width count := by
  change (BitWord.instruction (execution := model) (resizeOp input output)).eventTrace path.1 ++
    (PowerOfTwo.shiftInto (model := model) count output).eventTrace path.2 = _
  rw [BitWord.bitWord_instruction_eventTrace, PowerOfTwo.shiftInto_events]
  rfl

/-- Actual native scaling multiplicities equal the exact independent operation formula. -/
theorem into_resourcePool (count : Nat) (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (into (model := model) count input output).Path) :
    (into (model := model) count input output).resourcePool path =
      ResourcePool.ofList (scaleTrace (model := model) sourceWidth width count) :=
  congrArg ResourcePool.ofList (into_events count input output path)

/-- The actual scale emits one resize plus exactly the requested number of native shifts. -/
theorem into_eventCount (count : Nat) (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (into (model := model) count input output).Path) :
    ((into (model := model) count input output).eventTrace path).length = count + 1 := by
  rw [into_events]
  simp only [scaleTrace, PowerOfTwo.shiftTrace, List.length_append,
    List.length_singleton, List.length_replicate]
  omega

/-- The actual source resize precedes every native shift in the exact unit-duration depth. -/
theorem into_depth (count : Nat) (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (into (model := model) count input output).Path) :
    (into (model := model) count input output).depth (fun _ => 1) path = count + 1 := by
  change 1 + (PowerOfTwo.shiftInto (model := model) count output).depth (fun _ => 1) path.2 = _
  have shifted := PowerOfTwo.shiftInto_depth count output path.2
  omega

/-- Actual native scaling restores every borrowed entry jointly with its external reference. -/
theorem into_borrowedRestored (count : Nat) (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) count input output).BorrowedRestored Reference state
      ((into (model := model) count input output).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Circuit.borrowedRestored_classical (model := model)
      (BitWord.selectedApplication (execution := model) (resizeOp input output)) _)
    (PowerOfTwo.shiftInto_borrowedRestored count output Reference _)

/-- Every actual native scale instruction keeps the complete original context live. -/
theorem into_visited (count : Nat) (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (into (model := model) count input output).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (into (model := model) count input output).visitedContexts path) :
    visited = ctx := by
  change visited ∈ [ctx] ++
    (PowerOfTwo.shiftInto (model := model) count output).visitedContexts path.2 at present
  simp only [List.mem_append, List.mem_singleton] at present
  exact present.elim id (PowerOfTwo.shiftInto_visited count output path.2 visited)

/-- All original resident storage remains counted throughout actual native scaling. -/
theorem into_resident_le (count : Nat) (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (into (model := model) count input output).Path) :
    (into (model := model) count input output).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited count input output path visited present]

/-- All original auxiliary roles remain counted throughout actual native scaling. -/
theorem into_auxiliary_le (count : Nat) (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (into (model := model) count input output).Path) :
    (into (model := model) count input output).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited count input output path visited present]

end

end QuantumAlg.ClassicalRoutines.Word.PowerOfTwo.Scale
