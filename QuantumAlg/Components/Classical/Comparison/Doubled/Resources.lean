/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Comparison.Doubled

/-!
# Actual doubled-comparison resources

The native trace counts the shift, comparison and complement in actual order.
Every resource remains live, and all borrowed-reference correlations survive.
-/

namespace QuantumAlg.ClassicalRoutines.Comparison.Doubled

open Execution

noncomputable section

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Independent native instruction formula for comparison with a doubled word. -/
def comparisonTrace (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .shiftLeft width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .lessThan width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not))]

/-- Actual comparison events match the independent three-operation formula. -/
lemma compareInto_events (refs : Refs ctx width)
    (path : (compareInto (model := model) refs).Path) :
    (compareInto (model := model) refs).eventTrace path =
      comparisonTrace (model := model) width := by
  change (BitWord.instruction (execution := model) (doubleOp refs)).eventTrace path.1 ++
    ((BitWord.instruction (execution := model) (compareOp refs)).eventTrace path.2.1 ++
      (BitWord.instruction (execution := model) (complementOp refs)).eventTrace path.2.2) = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

/-- Actual native multiplicities come from the same independent three-operation formula. -/
lemma compareInto_resourcePool (refs : Refs ctx width)
    (path : (compareInto (model := model) refs).Path) :
    (compareInto (model := model) refs).resourcePool path =
      ResourcePool.ofList (comparisonTrace (model := model) width) := by
  unfold Circuit.resourcePool
  rw [compareInto_events]

/-- Actual serial depth includes the data dependence between all three operations. -/
lemma compareInto_depth (refs : Refs ctx width)
    (path : (compareInto (model := model) refs).Path) :
    (compareInto (model := model) refs).depth (fun _ => 1) path = 3 := rfl

/-- The actual comparison restores the complete borrowed-reference joint state. -/
lemma compareInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (compareInto (model := model) refs).BorrowedRestored Reference state
      ((compareInto (model := model) refs).execute environment Reference state) := by
  refine Circuit.borrowedRestored_seq (environment := environment)
    (BitWord.instruction (execution := model) (doubleOp refs)) _ state
    (Circuit.borrowedRestored_classical (environment := environment) _ state) ?_
  exact Circuit.borrowedRestored_seq
    (environment := environment) _ _ _
    (Circuit.borrowedRestored_classical (environment := environment) _ _)
    (Circuit.borrowedRestored_classical (environment := environment) _ _)

/-- All three actual instructions use the complete original context. -/
lemma compareInto_visited (refs : Refs ctx width)
    (path : (compareInto (model := model) refs).Path) :
    (compareInto (model := model) refs).visitedContexts path = List.replicate 3 ctx := rfl

/-- Resident accounting retains all caller-supplied quantum and classical resources. -/
lemma compareInto_resident_le (refs : Refs ctx width)
    (path : (compareInto (model := model) refs).Path) :
    (compareInto (model := model) refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [compareInto_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- Auxiliary roles are preserved and counted throughout the actual comparison. -/
lemma compareInto_auxiliary_le (refs : Refs ctx width)
    (path : (compareInto (model := model) refs).Path) :
    (compareInto (model := model) refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [compareInto_visited] at present
  rw [(List.mem_replicate.mp present).2]

end

end QuantumAlg.ClassicalRoutines.Comparison.Doubled
