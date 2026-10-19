/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Semantics
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# The complete original-store effect of the actual native square root

The exact source-to-output theorem and the frame of every other original
cell determine one mathematical write. All lexical scratch belongs to the
actual routine and disappears on exit. Consequently, subsequent recovery
steps receive their original parameters and previous results unchanged,
and the theorem permits the square-root input and output to share a cell.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

open Execution

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Every original structural read outside the actual final destination retains its entire value. -/
lemma nativeSqrt_into_read_unchanged (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) {shape : CShape}
    (other : CInputRef ctx shape) (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (intoStep (model := model) input output store).1.read other = store.read other := by
  let lifted := underRead other width
  let pushed := pushStore width store
  let saved := pushed.applyOp (widenOp input)
  let loaded := ConstantWord.foldStep (model := model) (halfCell ctx width)
    (List.ofFn (ConstantWord.constantBits width (initialHalf width))) saved
  let iterated := iteratedRoundStep (model := model) (.storage (wideCell ctx width).toCStorageRef)
    (roundRefs ctx width) width loaded.1
  have wideFree : (widenOp input).outputRef.key ∉ lifted.storageKeys :=
    nativeSqrt_underRead_free other width (wideCell ctx width).key (by simp [internalKeys])
  have halfFree : (halfCell ctx width).key ∉ lifted.storageKeys :=
    nativeSqrt_underRead_free other width _ (by simp [internalKeys])
  have roundFree : ∀ key ∈ writeKeys (roundRefs ctx width), key ∉ lifted.storageKeys := by
    intro key present
    change key ∈ [(candidateCell ctx width).key, (squareCell ctx width).key,
      (tooLargeCell ctx width).key, (rootCell ctx width).key, (halfCell ctx width).key] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl | rfl | rfl
    all_goals exact nativeSqrt_underRead_free other width _ (by simp [internalKeys])
  have finishFree : (finishOp output).outputRef.key ∉ lifted.storageKeys := by
    change (underWrite output width).key ∉ (underRead other width).storageKeys
    rw [nativeSqrt_underWrite_key, nativeSqrt_underRead_keys]
    exact separate
  have afterCopy := Store.read_applyOp_of_not_mem_storageKeys
    iterated.1 (finishOp output) lifted finishFree
  have afterRounds := nativeSqrt_iteration_read_unchanged (model := model)
    (.storage (wideCell ctx width).toCStorageRef) (roundRefs ctx width)
    lifted roundFree width loaded.1
  have afterLoader := ConstantWord.constantWord_fold_read_other (model := model) (halfCell ctx
    width)
    (List.ofFn (ConstantWord.constantBits width (initialHalf width))) lifted halfFree saved
  have afterWiden := Store.read_applyOp_of_not_mem_storageKeys
    pushed (widenOp input) lifted wideFree
  have entered := nativeSqrt_push_read other width store
  have exited := nativeSqrt_pop_read other width (bodyStep (model := model) input output pushed).1
  exact exited.trans
    (afterCopy.trans (afterRounds.trans (afterLoader.trans (afterWiden.trans entered))))

/-- The actual output value is the canonical unsigned word containing the exact square root. -/
lemma nativeSqrt_into_output_value (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (intoStep (model := model) input output store).1.read (.storage output.toCStorageRef) =
      CShape.wordOfNat width (Nat.sqrt (store.read input).toNat) := by
  have natural := nativeSqrt_into_read_output (model := model) input output store
  have bounded : Nat.sqrt (store.read input).toNat < 2 ^ width :=
    (Nat.sqrt_le_self _).trans_lt (store.read input).toNat_lt
  cases actual : (intoStep (model := model) input output store).1.read (.storage
    output.toCStorageRef) with
  | unsignedWord word =>
      apply congrArg CShape.Value.unsignedWord
      apply Fin.ext
      change word.val = Nat.sqrt (store.read input).toNat % 2 ^ width
      rw [Nat.mod_eq_of_lt bounded]
      simpa only [actual, CShape.Value.toNat] using natural

/-- The complete returned store changes precisely the actual caller destination. -/
lemma nativeSqrt_into_store (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (intoStep (model := model) input output store).1 =
      store.write output (CShape.wordOfNat width (Nat.sqrt (store.read input).toNat)) := by
  apply Store.store_eq_write_of_read_frame
  · exact nativeSqrt_into_output_value (model := model) input output store
  · intro shape other separate
    exact nativeSqrt_into_read_unchanged input output (.storage other)
      (by simpa only [CInputRef.storageKeys, List.mem_singleton] using separate) store

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
