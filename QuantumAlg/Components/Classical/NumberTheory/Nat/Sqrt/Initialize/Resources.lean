/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Initialize.Program
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Independent native resources of the actual square-root initialization
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt

open Execution

noncomputable section

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {inputWidth : Nat}

/-- Original independent resize, two clears, increment and fixed-shift coordinate budget. -/
def initializationEventEnvelope (inputWidth : Nat) : ResourcePool model :=
  ResourcePool.singleton (.classicalOperation
      (BitWord.selectedCoordinate (execution := model)
      (.wordResize inputWidth (workWidth inputWidth + workWidth inputWidth)))) +
    (ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor (workWidth inputWidth)))) +
      (ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor (workWidth inputWidth)))) +
        (ResourcePool.singleton
            (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment (workWidth inputWidth)))) +
          ResourcePool.scale (inputWidth - 1) (ResourcePool.singleton
            (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .shiftLeft (workWidth inputWidth))))))))

/-- Chronological original native instruction formula, independent of placement and store. -/
def initializationTrace (inputWidth : Nat) : List (Resource.Event model) :=
  .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize inputWidth (workWidth inputWidth + workWidth inputWidth))) ::
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor (workWidth inputWidth))) ::
      .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor (workWidth inputWidth))) ::
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment (workWidth inputWidth))) ::
          List.replicate (inputWidth - 1)
            (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .shiftLeft (workWidth inputWidth))))

/-- The actual initializer emits exactly the original independent instruction sequence. -/
lemma initializeInto_events (refs : Refs ctx inputWidth) (path : (initializeInto (model :=
  model) refs).Path) :
    (initializeInto (model := model) refs).eventTrace path = initializationTrace (model := model)
      inputWidth := by
  rcases path with ⟨resized, root, half, incremented, shifts⟩
  change Fin (inputWidth - 1) →
    (BitWord.instruction (execution := model) (shiftHalfOp refs)).Path at shifts
  change (BitWord.instruction (execution := model) (initializeResizeOp refs)).eventTrace resized ++
    ((BitWord.instruction (execution := model)
      (initializeClearOp refs.round.root)).eventTrace root ++
    ((BitWord.instruction (execution := model)
      (initializeClearOp refs.round.half)).eventTrace half ++
    ((BitWord.instruction (execution := model)
      (initializeIncrementOp refs)).eventTrace incremented ++
      (List.ofFn (fun index : Fin (inputWidth - 1) =>
        (BitWord.instruction (execution := model) (shiftHalfOp refs)).eventTrace
          (shifts index))).flatten))) = _
  simp only [BitWord.bitWord_instruction_eventTrace, List.ofFn_const]
  simp [initializationTrace, initializeResizeOp, initializeClearOp, initializeIncrementOp,
    shiftHalfOp, ClassicalOp.label]

/-- Native multiplicities equal the independent original initialization formula. -/
lemma initializeInto_resourcePool (refs : Refs ctx inputWidth)
    (path : (initializeInto (model := model) refs).Path) :
    (initializeInto (model := model) refs).resourcePool path = initializationEventEnvelope (model
      := model) inputWidth := by
  change ResourcePool.ofList ((initializeInto (model := model) refs).eventTrace path) = _
  rw [initializeInto_events]
  simp only [initializationTrace, ResourcePool.ofList_cons, ResourcePool.ofList_replicate,
    initializationEventEnvelope]

/-- Every actual initializer path satisfies its independent native coordinate bound. -/
lemma initializeInto_pool_le (refs : Refs ctx inputWidth) (path : (initializeInto (model :=
  model) refs).Path) :
    (initializeInto (model := model) refs).resourcePool path ≤ initializationEventEnvelope (model
      := model) inputWidth :=
  le_of_eq (initializeInto_resourcePool refs path)

/-- Four native setup instructions precede the exact fixed number of native shifts. -/
lemma initializeInto_eventCount (refs : Refs ctx inputWidth)
    (path : (initializeInto (model := model) refs).Path) :
    ((initializeInto (model := model) refs).eventTrace path).length = 4 + (inputWidth - 1) := by
  rw [initializeInto_events]
  simp only [initializationTrace, List.length_cons, List.length_replicate]
  omega

/-- Actual unit-duration depth includes all four setup writes and every dependent shift. -/
lemma initializeInto_depth (refs : Refs ctx inputWidth) (path : (initializeInto (model := model)
  refs).Path) :
    (initializeInto (model := model) refs).depth (fun _ => 1) path = 4 + (inputWidth - 1) := by
  have shifts : (∑ _ : Fin (inputWidth - 1), (1 : Nat)) = inputWidth - 1 := by simp
  change 1 + (1 + (1 + (1 + (0 + ∑ _ : Fin (inputWidth - 1), (1 : Nat))))) = _
  rw [shifts]
  omega

/-- All visited contexts are the complete original context throughout setup and iteration. -/
lemma initializeInto_visited (refs : Refs ctx inputWidth) (path : (initializeInto (model :=
  model) refs).Path)
    (visited : RuntimeCtx model.kind) (present : visited ∈ (initializeInto (model := model)
      refs).visitedContexts path) :
    visited = ctx := by
  have member : visited = ctx ∨ inputWidth - 1 ≠ 0 ∧ visited = ctx := by
    simpa [initializeInto, shiftHalfLoopInto, shiftHalfInto, BitWord.instruction,
      Circuit.visitedContexts,
      List.ofFn_const] using present
  exact member.elim id And.right

/-- Resident space retains every caller-supplied cell and quantum system. -/
lemma initializeInto_resident_le (refs : Refs ctx inputWidth)
    (path : (initializeInto (model := model) refs).Path) :
    (initializeInto (model := model) refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [initializeInto_visited refs path visited present]

/-- Auxiliary space follows the original workspace roles without hidden fresh cells. -/
lemma initializeInto_auxiliary_le (refs : Refs ctx inputWidth)
    (path : (initializeInto (model := model) refs).Path) :
    (initializeInto (model := model) refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [initializeInto_visited refs path visited present]

/-- Every charged initialization write restores the complete borrowed-reference joint state. -/
lemma initializeInto_borrowedRestored (refs : Refs ctx inputWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (initializeInto (model := model) refs).BorrowedRestored Reference state
      ((initializeInto (model := model) refs).execute environment Reference state) := by
  unfold initializeInto
  refine Circuit.borrowedRestored_seq
    (environment := environment) _ _ state (Circuit.borrowedRestored_classical (environment :=
    environment) _ _) ?_
  refine Circuit.borrowedRestored_seq
    (environment := environment) _ _ _ (Circuit.borrowedRestored_classical (environment :=
    environment) _ _) ?_
  refine Circuit.borrowedRestored_seq
    (environment := environment) _ _ _ (Circuit.borrowedRestored_classical (environment :=
    environment) _ _) ?_
  refine Circuit.borrowedRestored_seq
    (environment := environment) _ _ _ (Circuit.borrowedRestored_classical (environment :=
    environment) _ _) ?_
  exact Circuit.borrowedRestored_iterate
    (environment := environment) (shiftHalfInto (model := model) refs) Reference
    (by
      intro history _ current
      exact Circuit.borrowedRestored_classical (environment := environment) _ current)
    (inputWidth - 1) _

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt
