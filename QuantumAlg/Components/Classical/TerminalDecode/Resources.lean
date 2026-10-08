/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.TerminalDecode.Circuit
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Native budgets of the actual terminal decoder

Each append emits one shift and at most one increment. Bounds retain both
closed operation coordinates, their actual widths, and arbitrary event
durations. They apply to every path, including zero-width decoding, and use
only the already declared source and destination cells.
-/

namespace QuantumAlg.ClassicalRoutines.TerminalDecode

open ClassicalAlgorithms.TerminalDecode

noncomputable section

/-- Native coordinate of one target-width left shift. -/
def shiftEvent {model : ExecutionModel} [BitWord.Selected model]
    (width : Nat) : Resource.Event model :=
  .classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordUnary .shiftLeft width))

/-- Native coordinate of a selected target-width increment. -/
def incrementEvent {model : ExecutionModel} [BitWord.Selected model]
    (width : Nat) : Resource.Event model :=
  .classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordUnary .increment width))

/-- Independent coordinatewise allowance for one append. -/
def bitEnvelope {model : ExecutionModel} [BitWord.Selected model]
    (width : Nat) : ResourcePool model :=
  ResourcePool.singleton (shiftEvent (model := model) width) +
    ResourcePool.singleton (incrementEvent (model := model) width)

/-- At most one shift and one increment for each fixed source position. -/
def envelope {model : ExecutionModel} [BitWord.Selected model]
    (width : Nat) : ResourcePool model :=
  ResourcePool.scale width (bitEnvelope (model := model) width)

/-- One actual append respects both native operation coordinates. -/
theorem terminalDecode_bitRef_pool_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    {width : Nat} (input : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (bitRefRoutine (model := model) input output).Path) :
    (bitRefRoutine (model := model) input output).resourcePool path ≤
      bitEnvelope (model := model) width := by
  rcases path with ⟨shiftPath, value, branchPath⟩
  cases value with
  | bit bit =>
      cases bit
      · change ResourcePool.ofList
          ((BitWord.instruction (execution := model) (shiftOp width output)).eventTrace
            shiftPath ++ []) ≤ _
        rw [BitWord.bitWord_instruction_eventTrace]
        change ResourcePool.ofList [shiftEvent (model := model) width] ≤
          bitEnvelope (model := model) width
        simp only [ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero, bitEnvelope]
        exact le_self_add
      · change (BitWord.instruction (execution := model) (incrementOp width output)).Path
          at branchPath
        change ResourcePool.ofList
          ((BitWord.instruction (execution := model) (shiftOp width output)).eventTrace shiftPath ++
            (BitWord.instruction (execution := model) (incrementOp width output)).eventTrace
              branchPath) ≤ _
        rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
        change ResourcePool.ofList [shiftEvent (model := model) width,
          incrementEvent (model := model) width] ≤ bitEnvelope (model := model) width
        simp only [ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero, bitEnvelope]
        exact le_rfl

/-- The literal fold has the sum of its actual append pools. -/
theorem terminalDecode_fold_pool_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    {width : Nat} (output : CWriteRef ctx (OutputShape width))
    (inputs : List (CInputRef ctx .bit)) :
    ∀ path : (foldBitRefs (model := model) output inputs).Path,
      (foldBitRefs (model := model) output inputs).resourcePool path ≤
        ResourcePool.scale inputs.length (bitEnvelope (model := model) width) := by
  induction inputs with
  | nil =>
      intro path
      exact le_rfl
  | cons input rest ih =>
      intro path
      change ResourcePool.ofList
        ((bitRefRoutine (model := model) input output).eventTrace path.1 ++
          (foldBitRefs (model := model) output rest).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append]
      simp only [List.length_cons, ResourcePool.scale_succ]
      exact add_le_add (terminalDecode_bitRef_pool_le input output path.1) (ih path.2)

/-- Both declared bit orders use exactly the same independent fixed-width budget. -/
theorem terminalDecode_intoFromBitRefs_pool_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat} (order : BitOrder)
    (inputs : Fin width → CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (intoFromBitRefs (model := model) order inputs output).Path) :
    (intoFromBitRefs (model := model) order inputs output).resourcePool path ≤
      envelope (model := model) width := by
  simpa only [List.length_ofFn, intoFromBitRefs, envelope] using
    terminalDecode_fold_pool_le output
      (List.ofFn (fun index => inputs (sourceIndex order index))) path

/-- One append retains the data dependency from shift to selected increment. -/
theorem terminalDecode_bitRef_depth_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    {width : Nat} (input : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (duration : Resource.Event model → Nat)
    (path : (bitRefRoutine (model := model) input output).Path) :
    (bitRefRoutine (model := model) input output).depth duration path ≤
      duration (shiftEvent (model := model) width) +
        duration (incrementEvent (model := model) width) := by
  rcases path with ⟨shiftPath, value, branchPath⟩
  cases value with
  | bit bit =>
      cases bit
      · change (BitWord.instruction (execution := model) (shiftOp width output)).depth
          duration shiftPath + 0 ≤ _
        rw [BitWord.bitWord_instruction_depth]
        change duration (shiftEvent (model := model) width) + 0 ≤ _
        omega
      · change (BitWord.instruction (execution := model) (incrementOp width output)).Path
          at branchPath
        change (BitWord.instruction (execution := model) (shiftOp width output)).depth
          duration shiftPath +
          (BitWord.instruction (execution := model) (incrementOp width output)).depth
            duration branchPath ≤ _
        rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth]
        exact le_rfl

/-- The ordered fold adds every selected append's actual dependency depth. -/
theorem terminalDecode_fold_depth_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    {width : Nat} (output : CWriteRef ctx (OutputShape width))
    (inputs : List (CInputRef ctx .bit)) (duration : Resource.Event model → Nat) :
    ∀ path : (foldBitRefs (model := model) output inputs).Path,
      (foldBitRefs (model := model) output inputs).depth duration path ≤
        inputs.length * (duration (shiftEvent (model := model) width) +
        duration (incrementEvent (model := model) width)) := by
  induction inputs with
  | nil =>
      intro path
      exact Nat.zero_le _
  | cons input rest ih =>
      intro path
      change (bitRefRoutine (model := model) input output).depth duration path.1 +
        (foldBitRefs (model := model) output rest).depth duration path.2 ≤ _
      have first := terminalDecode_bitRef_depth_le input output duration path.1
      have later := ih path.2
      simp only [List.length_cons, Nat.succ_mul]
      omega

/-- Explicit fixed-width duration bound derived from the same actual paths. -/
theorem terminalDecode_intoFromBitRefs_depth_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat} (order : BitOrder)
    (inputs : Fin width → CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (duration : Resource.Event model → Nat)
    (path : (intoFromBitRefs (model := model) order inputs output).Path) :
    (intoFromBitRefs (model := model) order inputs output).depth duration path ≤
      width * (duration (shiftEvent (model := model) width) +
        duration (incrementEvent (model := model) width)) := by
  simpa only [List.length_ofFn, intoFromBitRefs] using terminalDecode_fold_depth_le output
    (List.ofFn (fun index => inputs (sourceIndex order index))) duration path

/-- No append allocates or removes a runtime entry, whichever bit is selected. -/
theorem terminalDecode_bitRef_visited {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    {width : Nat} (input : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (bitRefRoutine (model := model) input output).Path) :
    (bitRefRoutine (model := model) input output).visitedContexts path = [ctx, ctx] := by
  rcases path with ⟨shiftPath, value, branchPath⟩
  cases value with
  | bit bit => cases bit <;> rfl

/-- Every context visited by the full fold is its actual unchanged context. -/
theorem terminalDecode_fold_visited {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    {width : Nat} (output : CWriteRef ctx (OutputShape width))
    (inputs : List (CInputRef ctx .bit)) :
    ∀ (path : (foldBitRefs (model := model) output inputs).Path) (visited : RuntimeCtx model.kind),
      visited ∈ (foldBitRefs (model := model) output inputs).visitedContexts path →
        visited = ctx := by
  induction inputs with
  | nil =>
      intro path visited present
      exact List.mem_singleton.mp present
  | cons input rest ih =>
      intro path visited present
      change visited ∈ (bitRefRoutine (model := model) input output).visitedContexts path.1 ++
        (foldBitRefs (model := model) output rest).visitedContexts path.2 at present
      rcases List.mem_append.mp present with first | later
      · rw [terminalDecode_bitRef_visited] at first
        simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using first
      · exact ih path.2 visited later

/-- The same-context decoder uses no additional resident storage. -/
theorem terminalDecode_intoFromBitRefs_resident_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat} (order : BitOrder)
    (inputs : Fin width → CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (intoFromBitRefs (model := model) order inputs output).Path) :
    (intoFromBitRefs (model := model) order inputs output).peakResidentSpace path ≤
      ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  have same := terminalDecode_fold_visited output
    (List.ofFn (fun index => inputs (sourceIndex order index))) path visited present
  exact same ▸ le_rfl

/-- Its auxiliary peak consists only of the actual already-scoped auxiliary entries. -/
theorem terminalDecode_intoFromBitRefs_auxiliary_le {model : ExecutionModel}
    [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat} (order : BitOrder)
    (inputs : Fin width → CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (intoFromBitRefs (model := model) order inputs output).Path) :
    (intoFromBitRefs (model := model) order inputs output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  have same := terminalDecode_fold_visited output
    (List.ofFn (fun index => inputs (sourceIndex order index))) path visited present
  exact same ▸ le_rfl

end

end QuantumAlg.ClassicalRoutines.TerminalDecode
