/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.IntegerSqrt.Correctness
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Actual integer-square-root round resources and joint borrowed restoration

The independent six-operation formula includes the copy selected by the actual
stored flag. Both possible copies have the same native opcode. All original
resident and auxiliary storage stays live, and the complete borrowed state is
preserved jointly with arbitrary external references.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.IntegerSqrt

open Execution

noncomputable section

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Independent native operation formula for the original binary-refinement round. -/
def roundTrace (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.addCarry width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.mulFull width width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .lessThan (width + width))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.bit .not)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .shiftRight width))]

/-- Every actual branch path emits exactly the original six native operations. -/
lemma roundInto_events (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (path : (roundInto (model := model) input refs).Path) :
    (roundInto (model := model) input refs).eventTrace path = roundTrace (model := model) width :=
      by
  rcases path with ⟨prefixPath, ⟨flag, selected⟩, shifted⟩
  change (BitWord.instruction (execution := model) (rootOp refs flag.toBool)).Path at selected
  change (BitWord.instruction (execution := model) (addOp refs)).eventTrace prefixPath.1 ++
    ((BitWord.instruction (execution := model) (squareOp refs)).eventTrace prefixPath.2.1 ++
      ((BitWord.instruction (execution := model) (compareOp input refs)).eventTrace
        prefixPath.2.2.1 ++
        (BitWord.instruction (execution := model) (takeOp refs)).eventTrace prefixPath.2.2.2)) ++
    ((BitWord.instruction (execution := model) (rootOp refs flag.toBool)).eventTrace selected ++
      (BitWord.instruction (execution := model) (halfOp refs)).eventTrace shifted) = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

/-- Native multiplicities come from that same actual path and independent operation formula. -/
lemma roundInto_resourcePool (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (path : (roundInto (model := model) input refs).Path) :
    (roundInto (model := model) input refs).resourcePool path = ResourcePool.ofList (roundTrace
      (model := model) width) :=
  congrArg ResourcePool.ofList (roundInto_events input refs path)

/-- Each actual binary-refinement round performs exactly six native instructions. -/
lemma roundInto_eventCount (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (path : (roundInto (model := model) input refs).Path) :
    ((roundInto (model := model) input refs).eventTrace path).length = 6 := by
  rw [roundInto_events]
  rfl

/-- The exact native unit-duration depth includes all six original dependent operations. -/
lemma roundInto_depth (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (path : (roundInto (model := model) input refs).Path) :
    (roundInto (model := model) input refs).depth (fun _ => 1) path = 6 := rfl

/-- The original context stays live through every actual operation, including the selected copy. -/
lemma roundInto_visited (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (path : (roundInto (model := model) input refs).Path) :
    (roundInto (model := model) input refs).visitedContexts path = [ctx, ctx, ctx, ctx, ctx, ctx]
      := rfl

/-- All original classical entries and quantum dimensions remain counted throughout the round. -/
lemma roundInto_resident_le (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (path : (roundInto (model := model) input refs).Path) :
    (roundInto (model := model) input refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  simp only [roundInto_visited, List.mem_cons, List.not_mem_nil, or_false, or_self] at present
  rw [present]

/-- All original auxiliary roles remain counted through the complete actual round. -/
lemma roundInto_auxiliary_le (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (path : (roundInto (model := model) input refs).Path) :
    (roundInto (model := model) input refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  simp only [roundInto_visited, List.mem_cons, List.not_mem_nil, or_false, or_self] at present
  rw [present]

/-- Every actual prefix, selected copy and shift restores borrowed correlations jointly. -/
lemma roundInto_borrowedRestored (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (roundInto (model := model) input refs).BorrowedRestored Reference state
      ((roundInto (model := model) input refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_seq (environment := environment)
  · apply Circuit.borrowedRestored_seq (environment := environment)
    · exact Circuit.borrowedRestored_classical (environment := environment)
          (BitWord.selectedApplication (execution := model) (addOp refs)) _
    · apply Circuit.borrowedRestored_seq (environment := environment)
      · exact Circuit.borrowedRestored_classical (environment := environment)
          (BitWord.selectedApplication (execution := model) (squareOp refs)) _
      · exact Circuit.borrowedRestored_seq (environment := environment) _ _ _
          (Circuit.borrowedRestored_classical (environment := environment)
          (BitWord.selectedApplication (execution := model) (compareOp input refs)) _)
          (Circuit.borrowedRestored_classical (environment := environment)
          (BitWord.selectedApplication (execution := model) (takeOp refs)) _)
  · apply Circuit.borrowedRestored_seq (environment := environment)
    · apply Circuit.borrowedRestored_branch (environment := environment)
      intro value _history _ current
      exact Circuit.borrowedRestored_classical (environment := environment)
          (BitWord.selectedApplication (execution := model) (rootOp refs value.toBool)) current
    · exact Circuit.borrowedRestored_classical (environment := environment)
          (BitWord.selectedApplication (execution := model) (halfOp refs)) _

end

end QuantumAlg.ClassicalRoutines.NumberTheory.IntegerSqrt
