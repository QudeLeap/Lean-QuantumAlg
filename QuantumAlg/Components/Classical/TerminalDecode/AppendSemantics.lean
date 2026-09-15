/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.TerminalDecode.Circuit
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Exact state update of one terminal-bit append

The intermediate bit is read from the store produced by the real shift.
The full-state equation therefore holds even if a caller aliases that read
with the output word. The ordinary nonaliasing wire arrangement additionally
identifies this read with the original source bit. Each theorem preserves the
entire quantum-reference block; only the named classical word is written.
-/

namespace QuantumAlg.ClassicalRoutines.TerminalDecode

open Execution
open ClassicalAlgorithms.TerminalDecode

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def incrementChoiceStep {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (output : CWriteRef ctx (OutputShape width)) (value : CShape.Value .bit)
    (store : Store ctx) : Store ctx ×
      (if value.toBool then Circuit.classical (incrementOp width output)
        else Circuit.id ctx).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => (store.applyOp (incrementOp width output), ())

private theorem incrementChoice_execute {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (output : CWriteRef ctx (OutputShape width))
    (value : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (if value.toBool then Circuit.classical (incrementOp width output)
      else Circuit.id ctx).execute Reference state =
        state.mapClassical (fun entry =>
          ((incrementChoiceStep output value entry.1).1,
            (entry.2, (incrementChoiceStep output value entry.1).2))) := by
  cases value with
  | bit bit =>
      cases bit
      · simp only [CShape.Value.toBool, incrementChoiceStep]
        refine (Circuit.execute_id_mapClassical Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _
      · simp only [CShape.Value.toBool, incrementChoiceStep]
        refine (Circuit.execute_classical_mapClassical
          (incrementOp width output) Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _

/-- The concrete store and path obtained by shifting and reading its actual selected bit. -/
def appendStep {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (input : CInputRef ctx .bit) (output : CWriteRef ctx (OutputShape width))
    (store : Store ctx) : Store ctx × (bitRefRoutine input output).Path :=
  let shifted := store.applyOp (shiftOp width output)
  let choice := shifted.read input
  let selected := incrementChoiceStep output choice shifted
  (selected.1, ((), ⟨choice, selected.2⟩))

private theorem appendStep_store {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (input : CInputRef ctx .bit) (output : CWriteRef ctx (OutputShape width))
    (store : Store ctx) :
    (appendStep input output store).1 =
      if ((store.applyOp (shiftOp width output)).read input).toBool then
        (store.applyOp (shiftOp width output)).applyOp (incrementOp width output)
      else store.applyOp (shiftOp width output) := by
  dsimp only [appendStep]
  cases choice : (store.applyOp (shiftOp width output)).read input with
  | bit bit => cases bit <;> rfl

/-- The actual append circuit maps each complete input block to its exact store and path. -/
theorem terminalDecode_append_execute {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (input : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (bitRefRoutine input output).execute Reference state =
      state.mapClassical (fun entry =>
        ((appendStep input output entry.1).1, (entry.2, (appendStep input output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (.classical (shiftOp width output))
    (.branch input (fun value =>
      if value.toBool then .classical (incrementOp width output) else .id ctx))
    (fun store => (store.applyOp (shiftOp width output), ()))
    (fun store =>
      ((incrementChoiceStep output (store.read input) store).1,
        ⟨store.read input, (incrementChoiceStep output (store.read input) store).2⟩))
    (fun reference {_} _ initial => by
      refine (Circuit.execute_classical_mapClassical
        (shiftOp width output) reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (fun reference {_} _ initial => Circuit.execute_branch_mapClassical input _
      (incrementChoiceStep output) (incrementChoice_execute output) reference initial)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The exact overwritten word implements wrapping shift-and-append on its original source bit. -/
theorem terminalDecode_append_read_output {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (input : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) (store : Store ctx)
    (separate : output.key ∉ input.storageKeys) :
    ((appendStep input output store).1.read (writeInput output)).toNat =
      appendBit (store.read (writeInput output)).toNat (store.read input).toBool %
        CShape.wordModulus width := by
  have frame : (store.applyOp (shiftOp width output)).read input = store.read input :=
    Store.read_applyOp_of_not_mem_storageKeys store (shiftOp width output) input separate
  have shifted := Store.read_applyOp_output store (shiftOp width output)
  change (store.applyOp (shiftOp width output)).read (writeInput output) =
    CShape.wordShiftLeft width (store.read (writeInput output)) at shifted
  rw [appendStep_store, frame]
  cases sampled : store.read input with
  | bit bit =>
      cases bit
      · simpa only [appendBit, CShape.Value.toBool, Bool.false_eq_true, if_false,
          Bool.toNat_false, Nat.add_zero,
          CShape.wordShiftLeft, CShape.wordOfNat_val] using
          congrArg CShape.Value.toNat shifted
      · have incremented := Store.read_applyOp_output
          (store.applyOp (shiftOp width output)) (incrementOp width output)
        change ((store.applyOp (shiftOp width output)).applyOp
          (incrementOp width output)).read (writeInput output) =
            CShape.wordOfNat width
              (((store.applyOp (shiftOp width output)).read (writeInput output)).toNat + 1)
          at incremented
        rw [shifted] at incremented
        simpa only [appendBit, CShape.Value.toBool, if_true, Bool.toNat_true,
          CShape.wordShiftLeft, CShape.wordOfNat_val, Nat.add_mod, Nat.mod_mod] using
          congrArg CShape.Value.toNat incremented

/-- The same exact append preserves every structural read outside its only written word. -/
theorem terminalDecode_append_read_other {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} {observed : CShape} (input : CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) (store : Store ctx)
    (other : CInputRef ctx observed)
    (separate : output.key ∉ other.storageKeys) :
    (appendStep input output store).1.read other = store.read other := by
  have shifted : (store.applyOp (shiftOp width output)).read other = store.read other :=
    Store.read_applyOp_of_not_mem_storageKeys store (shiftOp width output) other separate
  rw [appendStep_store]
  split
  · exact (Store.read_applyOp_of_not_mem_storageKeys
      (store.applyOp (shiftOp width output)) (incrementOp width output) other separate).trans
      shifted
  · exact shifted

end

end QuantumAlg.ClassicalRoutines.TerminalDecode
