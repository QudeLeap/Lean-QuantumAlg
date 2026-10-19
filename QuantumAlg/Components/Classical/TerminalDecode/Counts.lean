/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.TerminalDecode.Trace
import all QuantumAlg.Core.Execution.Trace

/-!
# Exact shift count of the actual stored-bit decoder

Every visited bit is appended by one real shift before its optional increment.
The literal fold therefore emits exactly one shift per source position. This
count applies to every possible path and to either bit order, including width zero.
-/

namespace QuantumAlg.ClassicalRoutines.TerminalDecode

open ClassicalAlgorithms.TerminalDecode

/-- One actual append always shifts, independently of its stored bit value. -/
lemma terminalDecode_bitRef_shiftCount {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    {width : Nat} (input : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (bitRefRoutine (model := model) input output).Path) :
    ResourcePool.count (shiftEvent (model := model) width)
      ((bitRefRoutine (model := model) input output).resourcePool path) = 1 := by
  change ResourcePool.count (shiftEvent (model := model) width)
    (ResourcePool.ofList ((bitRefRoutine (model := model) input output).eventTrace path)) = _
  rw [bitRef_events]
  have distinct : Resource.ClassicalOpLabel.wordUnary .increment width ≠
      .wordUnary .shiftLeft width := by
    intro same
    cases same
  cases path.2.1.toBool <;>
    simp [bitTrace, shiftEvent, incrementEvent, BitWord.selectedCoordinate, distinct]

/-- The actual ordered fold contains exactly one shift for each original source reference. -/
lemma terminalDecode_fold_shiftCount {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    {width : Nat} (output : CWriteRef ctx (OutputShape width))
    (inputs : List (CInputRef ctx .bit)) :
    ∀ path : (foldBitRefs (model := model) output inputs).Path,
      ResourcePool.count (shiftEvent (model := model) width)
          ((foldBitRefs (model := model) output inputs).resourcePool path) =
        inputs.length := by
  induction inputs with
  | nil =>
      intro path
      change ResourcePool.count (shiftEvent (model := model) width) 0 = 0
      exact ResourcePool.count_zero _
  | cons input rest ih =>
      intro path
      change ResourcePool.count (shiftEvent (model := model) width) (ResourcePool.ofList
        ((bitRefRoutine (model := model) input output).eventTrace path.1 ++
          (foldBitRefs (model := model) output rest).eventTrace path.2)) = _
      rw [ResourcePool.ofList_append, ResourcePool.count_add]
      change ResourcePool.count (shiftEvent (model := model) width)
        ((bitRefRoutine (model := model) input output).resourcePool path.1) +
        ResourcePool.count (shiftEvent (model := model) width)
          ((foldBitRefs (model := model) output rest).resourcePool path.2) = _
      rw [terminalDecode_bitRef_shiftCount, ih]
      simp only [List.length_cons, Nat.add_comm]

/-- Both actual bit orders visit exactly the declared source width. -/
lemma terminalDecode_intoFromBitRefs_shiftCount {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat} (order : BitOrder)
    (inputs : Fin width → CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (intoFromBitRefs (model := model) order inputs output).Path) :
    ResourcePool.count (shiftEvent (model := model) width)
      ((intoFromBitRefs (model := model) order inputs output).resourcePool path) = width := by
  simpa only [List.length_ofFn, intoFromBitRefs] using
    terminalDecode_fold_shiftCount output
      (List.ofFn (fun index => inputs (sourceIndex order index))) path

/-- Retaining the output adds no arithmetic event to the exact-width shift count. -/
lemma terminalDecode_routine_shiftCount {model : ExecutionModel} [BitWord.Selected model]
    (ctx : RuntimeCtx model.kind) (width : Nat) (order : BitOrder)
    (input : CInputRef ctx (InputShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (routine (model := model) ctx width order input key fresh).Path) :
    ResourcePool.count (shiftEvent (model := model) width)
      ((routine (model := model) ctx width order input key fresh).resourcePool path) = width := by
  change ResourcePool.count (shiftEvent (model := model) width)
    ((intoFromBitRefs (model := model) order
      (fun bit => .bitsGet (input.underRetained key (OutputShape width) fresh) bit)
      (CWriteRef.retainedHead ctx key (OutputShape width) fresh)).resourcePool path.2) = width
  exact terminalDecode_intoFromBitRefs_shiftCount order _ _ path.2

end QuantumAlg.ClassicalRoutines.TerminalDecode
