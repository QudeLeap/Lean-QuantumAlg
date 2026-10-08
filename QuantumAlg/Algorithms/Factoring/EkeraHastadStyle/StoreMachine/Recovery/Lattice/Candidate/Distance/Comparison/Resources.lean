/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Distance.Comparison.Correctness

/-!
# Actual near-target comparison resources
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearTargetScale

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Independent original copy and three-shift instruction formula. -/
def copyScaleTrace (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordUnary .copy width))] ++
    List.replicate 3 (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .shiftLeft width)))

/-- Every actual copy-scale path emits the original four-instruction formula. -/
theorem copyScaleInto_events (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (copyScaleInto input output).Path) :
    (copyScaleInto input output).eventTrace path = copyScaleTrace width := by
  change (BitWord.instruction (execution := model) (copyOp input output)).eventTrace
      path.1 ++
    (ClassicalRoutines.Word.PowerOfTwo.shiftInto 3 output).eventTrace path.2 = _
  rw [BitWord.bitWord_instruction_eventTrace,
    ClassicalRoutines.Word.PowerOfTwo.shiftInto_events]
  rfl

/-- Independent original distance scale, square, range scale, addition and comparison schedule. -/
def scaleTrace (width : Nat) : List (Resource.Event model) :=
  copyScaleTrace width ++
    ([.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .mulLow width))] ++
      (copyScaleTrace width ++ [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .add width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .lessThan width))]))

/-- Every actual near-target path emits exactly the original eleven native instructions. -/
theorem scaleInto_events (refs : Refs ctx width) (path : (scaleInto refs).Path) :
    (scaleInto refs).eventTrace path = scaleTrace width := by
  change (copyScaleInto refs.distance refs.scaledDistance).eventTrace path.1 ++
    ((BitWord.instruction (execution := model) (squareOp refs)).eventTrace path.2.1 ++
      ((copyScaleInto (writeInput refs.rangeSquare) refs.scaledRange).eventTrace
          path.2.2.1 ++
        ((BitWord.instruction (execution := model) (addRangeOp refs)).eventTrace
            path.2.2.2.1 ++
          (BitWord.instruction (execution := model) (compareOp refs)).eventTrace
            path.2.2.2.2))) = _
  rw [copyScaleInto_events, copyScaleInto_events,
    BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace]
  rfl

/-- Actual native multiplicities equal the independently specified original instruction formula. -/
theorem scaleInto_resourcePool (refs : Refs ctx width) (path : (scaleInto refs).Path) :
    (scaleInto refs).resourcePool path = ResourcePool.ofList (scaleTrace width) :=
  congrArg ResourcePool.ofList (scaleInto_events refs path)

/-- Actual execution charges all eleven original native instructions. -/
theorem scaleInto_eventCount (refs : Refs ctx width) (path : (scaleInto refs).Path) :
    ((scaleInto refs).eventTrace path).length = 11 := by
  rw [scaleInto_events]
  rfl

/-- All eleven actual instructions contribute to the original sequential dependency depth. -/
theorem scaleInto_depth (refs : Refs ctx width) (path : (scaleInto refs).Path) :
    (scaleInto refs).depth (fun _ => 1) path = 11 := by
  change (1 + (ClassicalRoutines.Word.PowerOfTwo.shiftInto 3 refs.scaledDistance).depth
    (fun _ => 1) path.1.2) + (1 + ((1 +
      (ClassicalRoutines.Word.PowerOfTwo.shiftInto 3 refs.scaledRange).depth
        (fun _ => 1) path.2.2.1.2) + (1 + 1))) = 11
  rw [ClassicalRoutines.Word.PowerOfTwo.shiftInto_depth,
    ClassicalRoutines.Word.PowerOfTwo.shiftInto_depth]

/-- Actual copying and shifts preserve all borrowed-reference correlations jointly. -/
theorem copyScaleInto_borrowedRestored (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (copyScaleInto input output).BorrowedRestored Reference state
      ((copyScaleInto input output).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (Circuit.borrowedRestored_classical _ state)
    (ClassicalRoutines.Word.PowerOfTwo.shiftInto_borrowedRestored 3 output Reference _)

/-- Actual addition and comparison jointly restore every borrowed-reference state. -/
theorem finishInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (finishInto refs).BorrowedRestored Reference state
      ((finishInto refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (Circuit.borrowedRestored_classical _ state)
    (Circuit.borrowedRestored_classical _ _)

/-- Actual range composition preserves the complete original borrowed-reference joint state. -/
theorem rangeInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (rangeInto refs).BorrowedRestored Reference state
      ((rangeInto refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (copyScaleInto_borrowedRestored (writeInput refs.rangeSquare) refs.scaledRange Reference state)
    (finishInto_borrowedRestored refs Reference _)

/-- Actual squaring and range arithmetic restore the original borrowed-reference joint state. -/
theorem squareRangeInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (squareRangeInto refs).BorrowedRestored Reference state
      ((squareRangeInto refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Circuit.borrowedRestored_classical _ state)
    (rangeInto_borrowedRestored refs Reference _)

/-- Actual scale composition preserves the complete original borrowed-reference joint state. -/
theorem scaleInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (scaleInto refs).BorrowedRestored Reference state
      ((scaleInto refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (copyScaleInto_borrowedRestored refs.distance refs.scaledDistance Reference state)
    (squareRangeInto_borrowedRestored refs Reference _)

/-- The actual copy and repeated shifts visit only the original supplied context. -/
theorem copyScaleInto_visited (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (copyScaleInto input output).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (copyScaleInto input output).visitedContexts path) : visited = ctx := by
  change visited ∈ [ctx] ++
    (ClassicalRoutines.Word.PowerOfTwo.shiftInto 3 output).visitedContexts path.2 at present
  simp only [List.mem_append, List.mem_singleton] at present
  exact present.elim id
    (ClassicalRoutines.Word.PowerOfTwo.shiftInto_visited 3 output path.2 visited)

/-- Every instruction and loop boundary retains the original quantum and classical cells. -/
theorem scaleInto_visited (refs : Refs ctx width) (path : (scaleInto refs).Path)
    (visited : RuntimeCtx model.kind) (present : visited ∈ (scaleInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (copyScaleInto refs.distance refs.scaledDistance).visitedContexts path.1 ++
    ([ctx] ++ ((copyScaleInto (writeInput refs.rangeSquare) refs.scaledRange).visitedContexts
      path.2.2.1 ++ ([ctx] ++ [ctx]))) at present
  simp only [List.mem_append, List.mem_singleton, or_self] at present
  rcases present with distance | square | ranged | finished
  · exact copyScaleInto_visited _ _ path.1 visited distance
  · exact square
  · exact copyScaleInto_visited _ _ path.2.2.1 visited ranged
  · exact finished

/-- Resident accounting includes all original live quantum and classical storage. -/
theorem scaleInto_resident_le (refs : Refs ctx width) (path : (scaleInto refs).Path) :
    (scaleInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [scaleInto_visited refs path visited present]

/-- Auxiliary accounting retains all original roles without additional allocation. -/
theorem scaleInto_auxiliary_le (refs : Refs ctx width) (path : (scaleInto refs).Path) :
    (scaleInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [scaleInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearTargetScale
