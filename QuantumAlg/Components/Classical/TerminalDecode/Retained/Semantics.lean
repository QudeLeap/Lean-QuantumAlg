/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.TerminalDecode.FoldSemantics
import all QuantumAlg.Components.Classical.TerminalDecode.Retained
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Borrowed.Classical

/-!
# Complete execution of the retained terminal decoder

The result is allocated by the actual retained instruction and written by the
proved shift-and-increment fold. The full execution equation records every
source block, external-reference correlation and actual circuit path. The
result is the source decoder in either bit order, and every original classical
read is preserved. No zero accumulator or source-separation premise is added
to the retained interface: allocation supplies the disjoint output cell.
-/

namespace QuantumAlg.ClassicalRoutines.TerminalDecode

open Execution
open ClassicalAlgorithms.TerminalDecode

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The real retained allocation followed by the actual decoder's store and path. -/
def retainedStep {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat)
    (order : BitOrder) (input : CInputRef ctx (InputShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys) (store : Store ctx) :
    Store (ResultCtx ctx width key fresh) ×
      (routine ctx width order input key fresh).Path :=
  let decoded := foldStep (CWriteRef.retainedHead ctx key (OutputShape width) fresh)
    (List.ofFn (fun index => .bitsGet
      (input.underRetained key (OutputShape width) fresh) (sourceIndex order index)))
    (store.pushRetained key (OutputShape width) fresh)
  (decoded.1, ((), decoded.2))

/-- Every complete quantum-reference block follows the actual retained store update. -/
theorem terminalDecode_routine_execute {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (width : Nat) (order : BitOrder) (input : CInputRef ctx (InputShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (routine ctx width order input key fresh).execute Reference state =
      state.mapClassical (fun entry =>
        ((retainedStep ctx width order input key fresh entry.1).1,
          (entry.2, (retainedStep ctx width order input key fresh entry.1).2))) := by
  simp only [routine, Circuit.execute_seq, Circuit.execute_retain, into, intoFromBitRefs,
    terminalDecode_fold_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def, retainedStep]
  congr 1
  exact Subsingleton.elim _ _

/-- Fresh allocation derives the source separation required by the internal fold. -/
private theorem lifted_source_separate {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (width : Nat) (input : CInputRef ctx (InputShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys) (index : Fin width) :
    (CWriteRef.retainedHead ctx key (OutputShape width) fresh).key ∉
      (CInputRef.bitsGet (input.underRetained key (OutputShape width) fresh) index).storageKeys :=
  CInputRef.fresh_not_mem_storageKeys_underRetained input key (OutputShape width) fresh

/-- The actual freshly retained word equals the pure decoder of the original stored source. -/
theorem terminalDecode_retainedStep_read_output {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat) (order : BitOrder)
    (input : CInputRef ctx (InputShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (store : Store ctx) :
    decodeOutput ((retainedStep ctx width order input key fresh store).1.read
      (resultRef ctx width key fresh)) = eval (decodeInput order (store.read input)) := by
  apply Fin.ext
  rw [terminalDecode_decodeOutput_val]
  have decoded := terminalDecode_intoFromBitRefs_read_output order
    (fun index => CInputRef.bitsGet (input.underRetained key (OutputShape width) fresh) index)
    (CWriteRef.retainedHead ctx key (OutputShape width) fresh)
    (store.pushRetained key (OutputShape width) fresh)
    (lifted_source_separate ctx width input key fresh)
  refine decoded.trans ?_
  have source : decodeInputFromBitRefs order
      (store.pushRetained key (OutputShape width) fresh)
      (fun index => CInputRef.bitsGet
        (input.underRetained key (OutputShape width) fresh) index) =
      decodeInput order (store.read input) := by
    change (⟨order, fun index =>
      (((store.pushRetained key (OutputShape width) fresh).read
        (input.underRetained key (OutputShape width) fresh)).bitGet index).toBool⟩ :
      Input width) = _
    rw [Store.read_pushRetained_underRetained]
    cases store.read input
    rfl
  exact congrArg (fun value => (eval value).val) source

/-- Every original structural read survives the complete retained decoder. -/
theorem terminalDecode_retainedStep_read_original {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat) (order : BitOrder)
    (input : CInputRef ctx (InputShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (store : Store ctx) {shape : CShape} (observed : CInputRef ctx shape) :
    (retainedStep ctx width order input key fresh store).1.read
      (observed.underRetained key (OutputShape width) fresh) = store.read observed := by
  change (foldStep _ _ (store.pushRetained key (OutputShape width) fresh)).1.read _ = _
  rw [terminalDecode_fold_read_other _ _ _ _
    (CInputRef.fresh_not_mem_storageKeys_underRetained observed key (OutputShape width) fresh)]
  exact Store.read_pushRetained_underRetained store key (OutputShape width) fresh observed

private theorem appendStep_borrowed {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (input : CInputRef ctx .bit) (output : CWriteRef ctx (OutputShape width))
    (store : Store ctx) :
    (appendStep input output store).1.readBorrowedClassical = store.readBorrowedClassical := by
  rw [appendStep_store]
  split <;> simp only [Store.readBorrowedClassical_applyOp]

/-- The actual addressed-bit fold preserves every borrowed classical value. -/
theorem terminalDecode_foldStep_borrowed_values {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (output : CWriteRef ctx (OutputShape width))
    (inputs : List (CInputRef ctx .bit)) (store : Store ctx) :
    (foldStep output inputs store).1.readBorrowedClassical = store.readBorrowedClassical := by
  induction inputs generalizing store with
  | nil => rfl
  | cons input rest ih =>
      change (foldStep output rest (appendStep input output store).1).1.readBorrowedClassical = _
      rw [ih, appendStep_borrowed]

private theorem fold_borrowedRestored {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (output : CWriteRef ctx (OutputShape width))
    (inputs : List (CInputRef ctx .bit)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (foldBitRefs output inputs).BorrowedRestored Reference state
      ((foldBitRefs output inputs).execute Reference state) := by
  rw [Circuit.BorrowedRestored, observeBorrowedAfter_sameContext,
    terminalDecode_fold_execute]
  refine Eq.trans ?_ (observeBorrowed_mapClassical (ctx := ctx) (Reference := Reference)
    (H := History) (K := History × (foldBitRefs output inputs).Path) state
    (fun entry => ((foldStep output inputs entry.1).1,
      (entry.2, (foldStep output inputs entry.1).2)))
    (fun entry => terminalDecode_foldStep_borrowed_values output inputs entry.1))
  congr 1
  congr 1
  exact Subsingleton.elim _ _

/-- Classical decoding restores all borrowed storage jointly with the external reference. -/
theorem terminalDecode_routine_borrowedRestored {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat) (order : BitOrder)
    (input : CInputRef ctx (InputShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (routine ctx width order input key fresh).BorrowedRestored Reference state
      ((routine ctx width order input key fresh).execute Reference state) := by
  unfold routine
  apply Circuit.borrowedRestored_seq
  · exact Circuit.borrowedRestored_retain key (OutputShape width) fresh state
  · exact fold_borrowedRestored _ _ Reference _

end

end QuantumAlg.ClassicalRoutines.TerminalDecode
