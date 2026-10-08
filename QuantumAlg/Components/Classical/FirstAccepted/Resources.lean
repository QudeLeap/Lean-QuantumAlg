/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Circuit
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Actual native resources of first-accepted selection

Every path emits negation and conjunction. A taken path additionally emits
the word copy and Boolean latch copy. The four-event allowance is independent
of the execution, while actual trace and depth retain the selected branch.
Every visited context is the existing input context; no extra cell is allocated.
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The fixed two-instruction decision ledger. -/
def decisionEvents (model : ExecutionModel) [BitWord.Selected model] : List (Resource.Event model)
  :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .and))]

/-- The fixed two-copy allowance for the selected arm. -/
def copyEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat) : List
  (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .copy))]

/-- Independent native coordinate allowance for one selector step. -/
def nativeEnvelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) : ResourcePool
  model :=
  ResourcePool.ofList (decisionEvents model) + ResourcePool.ofList (copyEvents model width)

private theorem decision_trace (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (decisionBody (model := model) inputs refs).Path) :
    (decisionBody (model := model) inputs refs).eventTrace path = decisionEvents model := by
  change (BitWord.instruction (execution := model) (availableOp refs)).eventTrace path.1 ++
    (BitWord.instruction (execution := model) (takeOp inputs refs)).eventTrace path.2 = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

private theorem copy_trace (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (copyBody (model := model) inputs refs).Path) :
    (copyBody (model := model) inputs refs).eventTrace path = copyEvents model width := by
  change (BitWord.instruction (execution := model) (selectedCopyOp inputs refs)).eventTrace path.1
    ++
    (BitWord.instruction (execution := model) (acceptedCopyOp refs)).eventTrace path.2 = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

private theorem decision_depth (inputs : Inputs ctx width) (refs : Refs ctx width)
    (duration : Resource.Event model → Nat)
    (path : (decisionBody (model := model) inputs refs).Path) :
    (decisionBody (model := model) inputs refs).depth duration path =
      duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not))) +
        duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit
          .and))) := by
  change (BitWord.instruction (execution := model) (availableOp refs)).depth duration path.1 +
    (BitWord.instruction (execution := model) (takeOp inputs refs)).depth duration path.2 = _
  simp only [BitWord.bitWord_instruction_depth]
  rfl

private theorem copy_depth (inputs : Inputs ctx width) (refs : Refs ctx width)
    (duration : Resource.Event model → Nat)
    (path : (copyBody (model := model) inputs refs).Path) :
    (copyBody (model := model) inputs refs).depth duration path =
      duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary
        .copy width))) +
        duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit
          .copy))) := by
  change (BitWord.instruction (execution := model) (selectedCopyOp inputs refs)).depth duration
    path.1 +
    (BitWord.instruction (execution := model) (acceptedCopyOp refs)).depth duration path.2 = _
  simp only [BitWord.bitWord_instruction_depth]
  rfl

/-- The actual trace contains copies exactly on its recorded true branch. -/
theorem firstAccepted_eventTrace (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (circuit (model := model) inputs refs).Path) :
    (circuit (model := model) inputs refs).eventTrace path =
      decisionEvents model ++ (if path.2.1.toBool then copyEvents model width else []) := by
  rcases path with ⟨decision, ⟨value, selected⟩⟩
  cases value with
  | bit taken =>
      cases taken
      · change (decisionBody (model := model) inputs refs).eventTrace decision ++ [] = _
        rw [decision_trace]
        rfl
      · change (copyBody (model := model) inputs refs).Path at selected
        change (decisionBody (model := model) inputs refs).eventTrace decision ++
          (copyBody (model := model) inputs refs).eventTrace selected = _
        rw [decision_trace, copy_trace]
        rfl

/-- Every actual event coordinate is bounded by the independent four-operation allowance. -/
theorem firstAccepted_pool_le (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (circuit (model := model) inputs refs).Path) :
    (circuit (model := model) inputs refs).resourcePool path ≤ nativeEnvelope model width := by
  rw [Circuit.resourcePool, firstAccepted_eventTrace, ResourcePool.ofList_append]
  unfold nativeEnvelope
  apply add_le_add le_rfl
  split
  · exact le_rfl
  · exact zero_le

/-- The independent native allowance contains exactly four operations at every word width. -/
theorem firstAccepted_nativeEnvelope_card (model : ExecutionModel) [BitWord.Selected model] (width
  : Nat) :
    (nativeEnvelope model width).card = 4 := rfl

/-- Native durations follow the actual two decision instructions and optional two copies. -/
theorem firstAccepted_depth (inputs : Inputs ctx width) (refs : Refs ctx width)
    (duration : Resource.Event model → Nat) (path : (circuit (model := model) inputs refs).Path) :
    (circuit (model := model) inputs refs).depth duration path =
      duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not))) +
        duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit
          .and))) +
          (if path.2.1.toBool then
            duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
              (.wordUnary .copy width))) +
              duration (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit
                .copy))) else 0) := by
  rcases path with ⟨decision, ⟨value, selected⟩⟩
  cases value with
  | bit taken =>
      cases taken
      · change (decisionBody (model := model) inputs refs).depth duration decision + 0 = _
        rw [decision_depth]
        rfl
      · change (copyBody (model := model) inputs refs).Path at selected
        change (decisionBody (model := model) inputs refs).depth duration decision +
          (copyBody (model := model) inputs refs).depth duration selected = _
        rw [decision_depth, copy_depth]
        rfl

/-- Unit native durations give depth two or four according to the real branch path. -/
theorem firstAccepted_unit_depth (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (circuit (model := model) inputs refs).Path) :
    (circuit (model := model) inputs refs).depth (fun _ => 1) path =
      if path.2.1.toBool then 4 else 2 := by
  rw [firstAccepted_depth]
  split <;> rfl

/-- Every visited live context is the selector's existing context. -/
theorem firstAccepted_visited (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (circuit (model := model) inputs refs).Path) :
    ∀ visited ∈ (circuit (model := model) inputs refs).visitedContexts path, visited = ctx := by
  rcases path with ⟨decision, ⟨value, selected⟩⟩
  cases value with
  | bit taken =>
      cases taken <;> intro visited present
      · change visited ∈ [ctx, ctx, ctx] at present
        simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present
      · change visited ∈ [ctx, ctx, ctx, ctx] at present
        simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present

/-- The resident peak requires no storage beyond the real existing context. -/
theorem firstAccepted_resident_le (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (circuit (model := model) inputs refs).Path) :
    (circuit (model := model) inputs refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  exact (firstAccepted_visited inputs refs path visited present) ▸ le_rfl

/-- The same executed path requires no additional auxiliary cell. -/
theorem firstAccepted_auxiliary_le (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (circuit (model := model) inputs refs).Path) :
    (circuit (model := model) inputs refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  exact (firstAccepted_visited inputs refs path visited present) ▸ le_rfl

end

end QuantumAlg.ClassicalRoutines.FirstAccepted
