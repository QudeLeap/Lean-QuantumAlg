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

/-- Native coordinate of one target-width left shift. -/
def shiftEvent {kind : ProblemKind} (width : Nat) : Resource.Event kind :=
  .classicalOperation (.wordUnary .shiftLeft width)

/-- Native coordinate of a selected target-width increment. -/
def incrementEvent {kind : ProblemKind} (width : Nat) : Resource.Event kind :=
  .classicalOperation (.wordUnary .increment width)

/-- Independent coordinatewise allowance for one append. -/
def bitEnvelope {kind : ProblemKind} (width : Nat) : ResourcePool kind :=
  ResourcePool.singleton (shiftEvent width) + ResourcePool.singleton (incrementEvent width)

/-- At most one shift and one increment for each fixed source position. -/
def envelope {kind : ProblemKind} (width : Nat) : ResourcePool kind :=
  ResourcePool.scale width (bitEnvelope width)

/-- One actual append respects both native operation coordinates. -/
theorem terminalDecode_bitRef_pool_le {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (input : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (bitRefRoutine input output).Path) :
    (bitRefRoutine input output).resourcePool path ≤ bitEnvelope width := by
  rcases path with ⟨shiftPath, value, branchPath⟩
  cases value with
  | bit bit =>
      cases bit
      · change ResourcePool.ofList [shiftEvent width] ≤ bitEnvelope width
        simp only [ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero, bitEnvelope]
        exact le_self_add
      · change ResourcePool.ofList [shiftEvent width, incrementEvent width] ≤ bitEnvelope width
        simp only [ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero, bitEnvelope]
        exact le_rfl

/-- The literal fold has the sum of its actual append pools. -/
theorem terminalDecode_fold_pool_le {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (output : CWriteRef ctx (OutputShape width))
    (inputs : List (CInputRef ctx .bit)) :
    ∀ path : (foldBitRefs output inputs).Path,
      (foldBitRefs output inputs).resourcePool path ≤
        ResourcePool.scale inputs.length (bitEnvelope width) := by
  induction inputs with
  | nil =>
      intro path
      exact le_rfl
  | cons input rest ih =>
      intro path
      change ResourcePool.ofList
        ((bitRefRoutine input output).eventTrace path.1 ++
          (foldBitRefs output rest).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append]
      simp only [List.length_cons, ResourcePool.scale_succ]
      exact add_le_add (terminalDecode_bitRef_pool_le input output path.1) (ih path.2)

/-- Both declared bit orders use exactly the same independent fixed-width budget. -/
theorem terminalDecode_intoFromBitRefs_pool_le {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} (order : BitOrder)
    (inputs : Fin width → CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (intoFromBitRefs order inputs output).Path) :
    (intoFromBitRefs order inputs output).resourcePool path ≤ envelope width := by
  simpa only [List.length_ofFn, intoFromBitRefs, envelope] using
    terminalDecode_fold_pool_le output
      (List.ofFn (fun index => inputs (sourceIndex order index))) path

/-- One append retains the data dependency from shift to selected increment. -/
theorem terminalDecode_bitRef_depth_le {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (input : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (duration : Resource.Event kind → Nat) (path : (bitRefRoutine input output).Path) :
    (bitRefRoutine input output).depth duration path ≤
      duration (shiftEvent width) + duration (incrementEvent width) := by
  rcases path with ⟨shiftPath, value, branchPath⟩
  cases value with
  | bit bit =>
      cases bit
      · change duration (shiftEvent width) + 0 ≤ _
        omega
      · exact le_rfl

/-- The ordered fold adds every selected append's actual dependency depth. -/
theorem terminalDecode_fold_depth_le {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (output : CWriteRef ctx (OutputShape width))
    (inputs : List (CInputRef ctx .bit)) (duration : Resource.Event kind → Nat) :
    ∀ path : (foldBitRefs output inputs).Path,
      (foldBitRefs output inputs).depth duration path ≤
        inputs.length * (duration (shiftEvent width) + duration (incrementEvent width)) := by
  induction inputs with
  | nil =>
      intro path
      exact Nat.zero_le _
  | cons input rest ih =>
      intro path
      change (bitRefRoutine input output).depth duration path.1 +
        (foldBitRefs output rest).depth duration path.2 ≤ _
      have first := terminalDecode_bitRef_depth_le input output duration path.1
      have later := ih path.2
      simp only [List.length_cons, Nat.succ_mul]
      omega

/-- Explicit fixed-width duration bound derived from the same actual paths. -/
theorem terminalDecode_intoFromBitRefs_depth_le {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} (order : BitOrder)
    (inputs : Fin width → CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (duration : Resource.Event kind → Nat)
    (path : (intoFromBitRefs order inputs output).Path) :
    (intoFromBitRefs order inputs output).depth duration path ≤
      width * (duration (shiftEvent width) + duration (incrementEvent width)) := by
  simpa only [List.length_ofFn, intoFromBitRefs] using terminalDecode_fold_depth_le output
    (List.ofFn (fun index => inputs (sourceIndex order index))) duration path

/-- No append allocates or removes a runtime entry, whichever bit is selected. -/
theorem terminalDecode_bitRef_visited {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (input : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (bitRefRoutine input output).Path) :
    (bitRefRoutine input output).visitedContexts path = [ctx, ctx] := by
  rcases path with ⟨shiftPath, value, branchPath⟩
  cases value with
  | bit bit => cases bit <;> rfl

/-- Every context visited by the full fold is its actual unchanged context. -/
theorem terminalDecode_fold_visited {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (output : CWriteRef ctx (OutputShape width))
    (inputs : List (CInputRef ctx .bit)) :
    ∀ (path : (foldBitRefs output inputs).Path) (visited : RuntimeCtx kind),
      visited ∈ (foldBitRefs output inputs).visitedContexts path → visited = ctx := by
  induction inputs with
  | nil =>
      intro path visited present
      exact List.mem_singleton.mp present
  | cons input rest ih =>
      intro path visited present
      change visited ∈ (bitRefRoutine input output).visitedContexts path.1 ++
        (foldBitRefs output rest).visitedContexts path.2 at present
      rcases List.mem_append.mp present with first | later
      · rw [terminalDecode_bitRef_visited] at first
        simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using first
      · exact ih path.2 visited later

/-- The same-context decoder uses no additional resident storage. -/
theorem terminalDecode_intoFromBitRefs_resident_le {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} (order : BitOrder)
    (inputs : Fin width → CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (intoFromBitRefs order inputs output).Path) :
    (intoFromBitRefs order inputs output).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  have same := terminalDecode_fold_visited output
    (List.ofFn (fun index => inputs (sourceIndex order index))) path visited present
  exact same ▸ le_rfl

/-- Its auxiliary peak consists only of the actual already-scoped auxiliary entries. -/
theorem terminalDecode_intoFromBitRefs_auxiliary_le {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} (order : BitOrder)
    (inputs : Fin width → CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (intoFromBitRefs order inputs output).Path) :
    (intoFromBitRefs order inputs output).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  have same := terminalDecode_fold_visited output
    (List.ofFn (fun index => inputs (sourceIndex order index))) path visited present
  exact same ▸ le_rfl

end QuantumAlg.ClassicalRoutines.TerminalDecode
