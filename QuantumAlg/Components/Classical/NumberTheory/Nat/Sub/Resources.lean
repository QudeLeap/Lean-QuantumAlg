/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sub.Program
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Native resources and joint borrowed restoration for natural subtraction

Every actual path charges the comparison and exactly one selected write.
The original branch maximum bounds native coordinates independently of the
store, while resident and auxiliary accounting retain the complete context.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatSub

open Execution

noncomputable section

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Independent original comparison plus clear-or-subtract coordinate allowance. -/
def eventEnvelope (width : Nat) : ResourcePool model :=
  ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordBinary .lessThan width))) +
    ResourcePool.max
      (ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .bitXor width))))
      (ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .sub width))))

/-- Two chronological native events selected by the recorded actual comparison latch. -/
def nativeTrace (width : Nat) (underflow : Bool) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .lessThan width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary (if underflow then .bitXor else .sub) width))]

/-- The actual path emits exactly its independently selected two-instruction formula. -/
lemma into_events (refs : Refs ctx width) (path : (into (model := model) refs).Path) :
    (into (model := model) refs).eventTrace path = nativeTrace (model := model) width
      path.2.1.toBool := by
  rcases path with ⟨comparison, flag, selected⟩
  cases flag with
  | bit flag =>
      cases flag
      · change (BitWord.instruction (execution := model) (subtractOp refs)).Path at selected
        change (BitWord.instruction (execution := model) (compareOp refs)).eventTrace comparison ++
          (BitWord.instruction (execution := model) (subtractOp refs)).eventTrace selected = _
        simp only [BitWord.bitWord_instruction_eventTrace]
        rfl
      · change (BitWord.instruction (execution := model) (clearOp refs)).Path at selected
        change (BitWord.instruction (execution := model) (compareOp refs)).eventTrace comparison ++
          (BitWord.instruction (execution := model) (clearOp refs)).eventTrace selected = _
        simp only [BitWord.bitWord_instruction_eventTrace]
        rfl

/-- Actual native multiplicities come from the same comparison and selected output write. -/
lemma into_resourcePool (refs : Refs ctx width) (path : (into (model := model) refs).Path) :
    (into (model := model) refs).resourcePool path = ResourcePool.ofList (nativeTrace (model :=
      model) width path.2.1.toBool) :=
  congrArg ResourcePool.ofList (into_events refs path)

/-- Every actual path meets the original independent native coordinate envelope. -/
lemma into_pool_le (refs : Refs ctx width) (path : (into (model := model) refs).Path) :
    (into (model := model) refs).resourcePool path ≤ eventEnvelope (model := model) width := by
  rw [into_resourcePool]
  cases underflow : path.2.1.toBool
  · simp only [nativeTrace, Bool.false_eq_true, if_false, ResourcePool.ofList_cons,
      ResourcePool.ofList_nil, add_zero, eventEnvelope]
    exact add_le_add le_rfl (ResourcePool.le_max_right _ _)
  · simp only [nativeTrace, if_true, ResourcePool.ofList_cons, ResourcePool.ofList_nil,
      add_zero, eventEnvelope]
    exact add_le_add le_rfl (ResourcePool.le_max_left _ _)

/-- Exactly two native operations execute, including a charged clear on underflow. -/
lemma into_eventCount (refs : Refs ctx width) (path : (into (model := model) refs).Path) :
    ((into (model := model) refs).eventTrace path).length = 2 := by
  rw [into_events]
  rfl

/-- Unit-duration dependency depth includes comparison before the selected output write. -/
lemma into_depth (refs : Refs ctx width) (path : (into (model := model) refs).Path) :
    (into (model := model) refs).depth (fun _ => 1) path = 2 := by
  rcases path with ⟨comparison, flag, selected⟩
  cases flag with
  | bit flag => cases flag <;> rfl

/-- Both actual instructions keep the complete caller-supplied runtime context live. -/
lemma into_visited (refs : Refs ctx width) (path : (into (model := model) refs).Path) :
    (into (model := model) refs).visitedContexts path = List.replicate 2 ctx := by
  rcases path with ⟨comparison, flag, selected⟩
  cases flag with
  | bit flag => cases flag <;> rfl

/-- Resident accounting retains every supplied classical cell and quantum system. -/
lemma into_resident_le (refs : Refs ctx width) (path : (into (model := model) refs).Path) :
    (into (model := model) refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- Auxiliary accounting retains all original workspace roles without hidden allocation. -/
lemma into_auxiliary_le (refs : Refs ctx width) (path : (into (model := model) refs).Path) :
    (into (model := model) refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited] at present
  rw [(List.mem_replicate.mp present).2]

/-- Actual comparison and selected writing restore the full borrowed-reference joint state. -/
lemma into_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) refs).BorrowedRestored Reference state ((into (model := model)
      refs).execute environment Reference state) := by
  refine Circuit.borrowedRestored_seq
    (environment := environment) (BitWord.instruction (execution := model) (compareOp refs))
    (selectedInto (model := model) refs) state
    (Circuit.borrowedRestored_classical (environment := environment) _ state) ?_
  apply Circuit.borrowedRestored_branch
    (environment := environment) (writeInput refs.lessThan) (arm (model := model) refs)
    Reference
  intro flag History _ state
  cases flag with
  | bit flag =>
    cases flag <;> exact Circuit.borrowedRestored_classical
      (environment := environment) _ state

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSub
