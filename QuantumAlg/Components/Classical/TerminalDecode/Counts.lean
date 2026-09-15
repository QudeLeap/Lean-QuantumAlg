/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.TerminalDecode.Resources
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
theorem terminalDecode_bitRef_shiftCount {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (input : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (bitRefRoutine input output).Path) :
    ResourcePool.count (shiftEvent width) ((bitRefRoutine input output).resourcePool path) = 1 := by
  rcases path with ⟨shiftPath, value, branchPath⟩
  cases value with
  | bit value =>
      cases value
      · change ResourcePool.count (shiftEvent width) (ResourcePool.ofList [shiftEvent width]) = 1
        simp
      · change ResourcePool.count (shiftEvent width)
          (ResourcePool.ofList [shiftEvent width, incrementEvent width]) = 1
        simp [shiftEvent, incrementEvent]

/-- The actual ordered fold contains exactly one shift for each original source reference. -/
theorem terminalDecode_fold_shiftCount {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (output : CWriteRef ctx (OutputShape width))
    (inputs : List (CInputRef ctx .bit)) :
    ∀ path : (foldBitRefs output inputs).Path,
      ResourcePool.count (shiftEvent width) ((foldBitRefs output inputs).resourcePool path) =
        inputs.length := by
  induction inputs with
  | nil =>
      intro path
      change ResourcePool.count (shiftEvent width) 0 = 0
      exact ResourcePool.count_zero _
  | cons input rest ih =>
      intro path
      change ResourcePool.count (shiftEvent width) (ResourcePool.ofList
        ((bitRefRoutine input output).eventTrace path.1 ++
          (foldBitRefs output rest).eventTrace path.2)) = _
      rw [ResourcePool.ofList_append, ResourcePool.count_add]
      change ResourcePool.count (shiftEvent width)
        ((bitRefRoutine input output).resourcePool path.1) +
        ResourcePool.count (shiftEvent width) ((foldBitRefs output rest).resourcePool path.2) = _
      rw [terminalDecode_bitRef_shiftCount, ih]
      simp only [List.length_cons, Nat.add_comm]

/-- Both actual bit orders visit exactly the declared source width. -/
theorem terminalDecode_intoFromBitRefs_shiftCount {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} (order : BitOrder)
    (inputs : Fin width → CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width))
    (path : (intoFromBitRefs order inputs output).Path) :
    ResourcePool.count (shiftEvent width)
      ((intoFromBitRefs order inputs output).resourcePool path) = width := by
  simpa only [List.length_ofFn, intoFromBitRefs] using
    terminalDecode_fold_shiftCount output
      (List.ofFn (fun index => inputs (sourceIndex order index))) path

/-- Retaining the output adds no arithmetic event to the exact-width shift count. -/
theorem terminalDecode_routine_shiftCount {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat) (order : BitOrder)
    (input : CInputRef ctx (InputShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (routine ctx width order input key fresh).Path) :
    ResourcePool.count (shiftEvent width)
      ((routine ctx width order input key fresh).resourcePool path) = width := by
  change ResourcePool.count (shiftEvent width)
    ((intoFromBitRefs order
      (fun bit => .bitsGet (input.underRetained key (OutputShape width) fresh) bit)
      (CWriteRef.retainedHead ctx key (OutputShape width) fresh)).resourcePool path.2) = width
  exact terminalDecode_intoFromBitRefs_shiftCount order _ _ path.2

end QuantumAlg.ClassicalRoutines.TerminalDecode
