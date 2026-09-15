/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.TerminalDecode.AppendSemantics
import all QuantumAlg.Util.Classical.TerminalDecode.Accumulator

/-!
# Exact full-state execution of the terminal decoder fold

The semantic fold records the actual path of each shift and selected increment.
Its equation is proved by composing the existing circuit executions. Structural
source separation then identifies the final written word with the original
fixed-width decoder, for every initial accumulator value.
-/

namespace QuantumAlg.ClassicalRoutines.TerminalDecode

open Execution
open ClassicalAlgorithms.TerminalDecode

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Actual store and path obtained by the literal ordered append circuit. -/
def foldStep {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (output : CWriteRef ctx (OutputShape width)) :
    (inputs : List (CInputRef ctx .bit)) → Store ctx →
      Store ctx × (foldBitRefs output inputs).Path
  | [], store => (store, ())
  | input :: rest, store =>
      let first := appendStep input output store
      let later := foldStep output rest first.1
      (later.1, (first.2, later.2))

/-- Actual sequential interpretation agrees on every complete quantum-reference block. -/
theorem terminalDecode_fold_execute {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (output : CWriteRef ctx (OutputShape width))
    (inputs : List (CInputRef ctx .bit)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (foldBitRefs output inputs).execute Reference state =
      state.mapClassical (fun entry =>
        ((foldStep output inputs entry.1).1, (entry.2, (foldStep output inputs entry.1).2))) := by
  induction inputs generalizing Reference History with
  | nil =>
      refine (Circuit.execute_id_mapClassical Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _
  | cons input rest ih =>
      refine (Circuit.execute_seq_mapClassical (bitRefRoutine input output)
        (foldBitRefs output rest) (appendStep input output) (foldStep output rest)
        (terminalDecode_append_execute input output)
        (fun reference {_} _ initial => by
          exact ih reference initial)
        Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _

/-- Every non-output structural read is preserved through the complete fold. -/
theorem terminalDecode_fold_read_other {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} {observed : CShape} (output : CWriteRef ctx (OutputShape width))
    (inputs : List (CInputRef ctx .bit)) (store : Store ctx)
    (other : CInputRef ctx observed) (separate : output.key ∉ other.storageKeys) :
    (foldStep output inputs store).1.read other = store.read other := by
  induction inputs generalizing store with
  | nil => rfl
  | cons input rest ih =>
      change (foldStep output rest (appendStep input output store).1).1.read other = _
      rw [ih]
      exact terminalDecode_append_read_other input output store other separate

/-- The actual output word follows the wrapping arithmetic of each executed append. -/
theorem terminalDecode_fold_read_output {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (output : CWriteRef ctx (OutputShape width))
    (inputs : List (CInputRef ctx .bit)) (store : Store ctx)
    (separate : ∀ input ∈ inputs, output.key ∉ input.storageKeys) :
    ((foldStep output inputs store).1.read (writeInput output)).toNat =
      (inputs.map (fun input => (store.read input).toBool)).foldl
        (fun value bit => appendBit value bit % CShape.wordModulus width)
        (store.read (writeInput output)).toNat := by
  induction inputs generalizing store with
  | nil => rfl
  | cons input rest ih =>
      have firstSeparate := separate input (.head rest)
      have laterSeparate : ∀ other ∈ rest, output.key ∉ other.storageKeys :=
        fun other present => separate other (.tail input present)
      have unchanged : rest.map (fun other =>
          ((appendStep input output store).1.read other).toBool) =
          rest.map (fun other => (store.read other).toBool) := by
        apply List.map_congr_left
        intro other present
        exact congrArg CShape.Value.toBool
          (terminalDecode_append_read_other input output store other
            (laterSeparate other present))
      change ((foldStep output rest (appendStep input output store).1).1.read
        (writeInput output)).toNat = _
      rw [ih _ laterSeparate, unchanged,
        terminalDecode_append_read_output input output store firstSeparate]
      rfl

/-- The whole width removes every initial accumulator contribution and writes exactly
the source's declared bit-order decoding. Source separation is internal wiring. -/
theorem terminalDecode_intoFromBitRefs_read_output {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} (order : BitOrder)
    (inputs : Fin width → CInputRef ctx .bit)
    (output : CWriteRef ctx (OutputShape width)) (store : Store ctx)
    (separate : ∀ index, output.key ∉ (inputs index).storageKeys) :
    ((foldStep output (List.ofFn (fun index => inputs (sourceIndex order index))) store).1.read
      (writeInput output)).toNat = (eval (decodeInputFromBitRefs order store inputs)).val := by
  rw [terminalDecode_fold_read_output output _ store (by
    intro input present
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
    exact separate (sourceIndex order index))]
  have sourceBits :
      (List.ofFn (fun index => inputs (sourceIndex order index))).map
          (fun input => (store.read input).toBool) =
        List.ofFn (accumulatorBits order (fun index => (store.read (inputs index)).toBool)) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext index
    simpa only [Function.comp_apply] using
      terminalDecode_sourceIndex_accumulatorBits order
        (fun index => (store.read (inputs index)).toBool) index
  rw [sourceBits]
  have initialBound := CShape.Value.toNat_lt (store.read (writeInput output))
  have result := terminalAccumulator_decodes
    (decodeInputFromBitRefs order store inputs) (store.read (writeInput output)).toNat
  simpa only [CShape.wordModulus, Nat.mod_eq_of_lt initialBound,
    decodeInputFromBitRefs, eval] using result

end

end QuantumAlg.ClassicalRoutines.TerminalDecode
