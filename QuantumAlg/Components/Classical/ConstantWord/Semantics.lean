/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.ConstantWord.Circuit
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Util.Classical.TerminalDecode.Accumulator

/-!
# Exact constant loading from arbitrary initial target words

The full-state equations follow the actual shift and selected increment paths.
The target width's number of shifts removes every previous target bit under
the same wrapping arithmetic used by the instructions. The final natural
value is the compilation parameter modulo the word modulus at every width.
All other structural reads and every complete quantum-reference block remain
unchanged.
-/

namespace QuantumAlg.ClassicalRoutines.ConstantWord

open Execution
open ClassicalAlgorithms.TerminalDecode

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Store and exact path of the literal shift and compile-selected increment. -/
def appendStep (output : CWriteRef ctx (.unsignedWord width)) :
    (bit : Bool) → Store ctx → Store ctx × (append (model := model) output bit).Path
  | false, store =>
      let first := BitWord.instructionStep (execution := model) (shiftOp output) store
      (first.1, (first.2, ()))
  | true, store =>
      let first := BitWord.instructionStep (execution := model) (shiftOp output) store
      let last := BitWord.instructionStep (execution := model) (incrementOp output) first.1
      (last.1, (first.2, last.2))

/-- Every compiled bit follows its actual instruction sequence on the full joint state. -/
lemma constantWord_append_execute (output : CWriteRef ctx (.unsignedWord width))
    (bit : Bool) {environment : model.Environment}
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (append (model := model) output bit).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := appendStep (model := model) output bit entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  cases bit <;>
    simp only [append, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
      Circuit.execute_id_mapClassical, State.mapHistory]
  all_goals
    repeat' rw [ExecutionState.executionState_mapClassical_comp_instances
      (result := inferInstance)]
    exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual appended target has exactly the wrapping shift-and-bit arithmetic. -/
lemma constantWord_append_read (output : CWriteRef ctx (.unsignedWord width))
    (bit : Bool) (store : Store ctx) :
    ((appendStep (model := model) output bit store).1.read (targetRead output)).toNat =
      appendBit (store.read (targetRead output)).toNat bit % 2 ^ width := by
  have shifted := Store.read_applyOp_output store (shiftOp output)
  change (store.applyOp (shiftOp output)).read (targetRead output) =
    CShape.wordShiftLeft width (store.read (targetRead output)) at shifted
  cases bit
  · simpa only [appendStep, BitWord.instructionStep, appendBit, Bool.toNat_false, Nat.add_zero,
      CShape.wordShiftLeft, CShape.wordOfNat_val, CShape.wordModulus] using
        congrArg CShape.Value.toNat shifted
  · have incremented := Store.read_applyOp_output
      (store.applyOp (shiftOp output)) (incrementOp output)
    change ((store.applyOp (shiftOp output)).applyOp (incrementOp output)).read
      (targetRead output) = CShape.wordOfNat width
        (((store.applyOp (shiftOp output)).read (targetRead output)).toNat + 1) at incremented
    rw [shifted] at incremented
    simpa only [appendStep, BitWord.instructionStep, appendBit, Bool.toNat_true,
      CShape.wordShiftLeft, CShape.wordOfNat_val, CShape.wordModulus,
      Nat.add_mod, Nat.mod_mod] using
        congrArg CShape.Value.toNat incremented

/-- The literal compiled bit writes only its actual supplied target cell. -/
lemma constantWord_append_read_other (output : CWriteRef ctx (.unsignedWord width))
    (bit : Bool) {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (appendStep (model := model) output bit store).1.read other = store.read other := by
  cases bit
  · exact Store.read_applyOp_of_not_mem_storageKeys store (shiftOp output) other separate
  · exact (Store.read_applyOp_of_not_mem_storageKeys _ (incrementOp output) other separate).trans
      (Store.read_applyOp_of_not_mem_storageKeys store (shiftOp output) other separate)

/-- The real store and nested path of the literal compilation-time list. -/
def foldStep (output : CWriteRef ctx (.unsignedWord width)) :
    (bits : List Bool) → Store ctx → Store ctx × (fold (model := model) output bits).Path
  | [], store => (store, ())
  | bit :: remaining, store =>
      let first := appendStep (model := model) output bit store
      let last := foldStep output remaining first.1
      (last.1, (first.2, last.2))

/-- The complete literal fold preserves every incoming quantum-reference matrix block. -/
lemma constantWord_fold_execute (output : CWriteRef ctx (.unsignedWord width))
    (bits : List Bool) {environment : model.Environment}
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (fold (model := model) output bits).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := foldStep (model := model) output bits entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  induction bits generalizing Reference History with
  | nil =>
      exact (Circuit.execute_id_mapClassical
        (environment := environment) (model := model) Reference state).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  | cons bit remaining ih =>
      refine (Circuit.execute_seq_mapClassical (environment := environment)
        (append (model := model) output bit) (fold (model := model) output remaining)
        (fun before =>
          let result := appendStep (model := model) output bit before.1
          ((result.1, before.2), result.2))
        (fun before =>
          let result := foldStep (model := model) output remaining before.1
          ((result.1, before.2), result.2)) ?_ ?_ Reference state).trans ?_
      · intro reference history _ input
        exact (constantWord_append_execute (model := model) output bit reference input).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)
      · intro reference history _ input
        exact (ih reference input).trans (ExecutionState.executionState_mapClassical_congr _ rfl)
      · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Target reads of the genuine fold obey the existing pure wrapping accumulator. -/
lemma constantWord_fold_read (output : CWriteRef ctx (.unsignedWord width))
    (bits : List Bool) (store : Store ctx) :
    ((foldStep (model := model) output bits store).1.read (targetRead output)).toNat =
      bits.foldl (fun value bit => appendBit value bit % 2 ^ width)
        (store.read (targetRead output)).toNat := by
  induction bits generalizing store with
  | nil => rfl
  | cons bit remaining ih =>
      change ((foldStep (model := model) output remaining
        (appendStep (model := model) output bit store).1).1.read
        (targetRead output)).toNat = _
      rw [ih, List.foldl_cons, constantWord_append_read]

/-- All structural reads outside the target survive the complete actual word loading. -/
lemma constantWord_fold_read_other (output : CWriteRef ctx (.unsignedWord width))
    (bits : List Bool) {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (foldStep (model := model) output bits store).1.read other = store.read other := by
  induction bits generalizing store with
  | nil => rfl
  | cons bit remaining ih =>
      change (foldStep (model := model) output remaining
        (appendStep (model := model) output bit store).1).1.read other = _
      exact (ih _).trans
        (constantWord_append_read_other (model := model) output bit other separate store)

/-- Width-many actual shifts load the exact compilation parameter modulo the target width. -/
lemma constantWord_read (output : CWriteRef ctx (.unsignedWord width))
    (constant : Nat) (store : Store ctx) :
    ((foldStep (model := model) output (List.ofFn (constantBits width constant)) store).1.read
      (targetRead output)).toNat = constant % 2 ^ width := by
  rw [constantWord_fold_read]
  have accumulated := terminalAccumulator_width_result (constantBits width constant)
    (store.read (targetRead output)).toNat
  rw [Nat.mod_eq_of_lt (CShape.Value.toNat_lt (store.read (targetRead output)))] at accumulated
  have bits : constantBits width constant ∘ Fin.rev =
      fun index : Fin width => constant.testBit index.val := by
    funext index
    simp only [Function.comp_apply, constantBits, Fin.rev_rev]
  rw [bits, Nat.ofBits_testBit] at accumulated
  exact accumulated

end

end QuantumAlg.ClassicalRoutines.ConstantWord
