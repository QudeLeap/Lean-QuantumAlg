/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sub.Execution
import all QuantumAlg.Components.Classical.NumberTheory.Native.Sub.Readout
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Exact original-store effect of the native saturating subtraction

The fresh comparison bit cannot overlap any original structural operand.
Both actual branches therefore implement natural-number subtraction on the
original reads, with zero on underflow. The final complete store is exactly
one write to the original destination; every other cell keeps its value.
The destination may alias either operand, and width zero requires no exception.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSub

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem decision_fresh {shape : CShape} (input : CInputRef ctx shape) :
    (decision ctx).key ∉ (underRead input).storageKeys := by
  have keys := CInputRef.storageKeys_underWorkspace input ctx.canonicalFreshKey .bit
    ctx.canonicalFreshKey_fresh
  intro present
  have original : ctx.canonicalFreshKey ∈ input.storageKeys :=
    (congrArg (fun storage => ctx.canonicalFreshKey ∈ storage) keys).mp present
  exact ctx.canonicalFreshKey_fresh (input.storageKeys_subset_context original)

/-- The real comparison leaves every original structural operand unchanged. -/
theorem nativeSub_compare_read_unchanged (left right : CInputRef ctx (.unsignedWord width))
    {shape : CShape} (other : CInputRef ctx shape) (store : Store (context ctx)) :
    (store.applyOp (compareOp left right)).read (underRead other) =
      store.read (underRead other) :=
  Store.read_applyOp_of_not_mem_storageKeys store (compareOp left right) (underRead other)
    (decision_fresh other)

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

private theorem branch_store (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (context ctx)) :
    (branchStep (model := model) left right output store).1 =
      if (store.read (.storage (decision ctx).toCStorageRef)).toBool then
        store.applyOp (clearOp output)
      else store.applyOp (subtractOp left right output) := by
  unfold branchStep
  cases flagRead : store.read (.storage (decision ctx).toCStorageRef) with
  | bit flag => cases flag <;> rfl

/-- The actual branch implements the truncated natural difference on the pre-comparison reads. -/
theorem nativeSub_body_read_output (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (context ctx)) :
    ((bodyStep (model := model) left right output store).1.read
      (.storage (underWrite output).toCStorageRef)).toNat =
      (store.read (underRead left)).toNat - (store.read (underRead right)).toNat := by
  let compared := store.applyOp (compareOp left right)
  have leftRead := nativeSub_compare_read_unchanged left right left store
  have rightRead := nativeSub_compare_read_unchanged left right right store
  have selected := branch_store (model := model) left right output compared
  rw [nativeSub_compare_read] at selected
  simp only [decide_eq_true_eq] at selected
  change ((branchStep (model := model) left right output compared).1.read
    (.storage (underWrite output).toCStorageRef)).toNat = _
  rw [selected]
  by_cases underflow : (store.read (underRead left)).toNat <
      (store.read (underRead right)).toNat
  · rw [if_pos underflow, nativeSub_clear_read]
    exact (Nat.sub_eq_zero_of_le underflow.le).symm
  · rw [if_neg underflow]
    have ordered : (compared.read (underRead right)).toNat ≤
        (compared.read (underRead left)).toNat := by
      rw [leftRead, rightRead]
      exact Nat.le_of_not_gt underflow
    exact (nativeSub_subtract_read left right output compared ordered).trans
      (congrArg₂ (fun first second : CShape.Value (.unsignedWord width) =>
        first.toNat - second.toNat) leftRead rightRead)

/-- Scope exit returns the exact natural difference of the caller's original operands. -/
theorem nativeSub_into_read_output (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((intoStep (model := model) left right output store).1.read (.storage
      output.toCStorageRef)).toNat =
      (store.read left).toNat - (store.read right).toNat := by
  let entered := store.pushWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
  have exited := congrArg CShape.Value.toNat
    (Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey .bit
      ctx.canonicalFreshKey_fresh (bodyStep (model := model) left right output entered).1
      (.storage output.toCStorageRef))
  have leftRead := Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey .bit
    ctx.canonicalFreshKey_fresh left
  have rightRead := Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey .bit
    ctx.canonicalFreshKey_fresh right
  exact exited.trans ((nativeSub_body_read_output (model := model) left right output entered).trans
    (congrArg₂ (fun first second : CShape.Value (.unsignedWord width) =>
      first.toNat - second.toNat) leftRead rightRead))

/-- Every original structural read outside the real destination retains its complete value. -/
theorem nativeSub_into_read_unchanged (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) {shape : CShape}
    (other : CInputRef ctx shape) (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (intoStep (model := model) left right output store).1.read other = store.read other := by
  let entered : Store (context ctx) :=
    store.pushWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
  let compared : Store (context ctx) := entered.applyOp (compareOp left right)
  have keys : (underRead other).storageKeys = other.storageKeys :=
    CInputRef.storageKeys_underWorkspace other ctx.canonicalFreshKey .bit
      ctx.canonicalFreshKey_fresh
  have outputFree : (underWrite output).key ∉ (underRead other).storageKeys := by
    change output.key ∉ (underRead other).storageKeys
    rw [keys]
    exact separate
  have afterBranch : (branchStep (model := model) left right output compared).1.read (underRead
    other) =
      compared.read (underRead other) := by
    refine (congrArg (fun current : Store (context ctx) => current.read (underRead other))
      (branch_store (model := model) left right output compared)).trans ?_
    split
    · exact Store.read_applyOp_of_not_mem_storageKeys
        compared (clearOp output) (underRead other) outputFree
    · exact Store.read_applyOp_of_not_mem_storageKeys
        compared (subtractOp left right output) (underRead other) outputFree
  have afterCompare := nativeSub_compare_read_unchanged left right other entered
  have pushed := Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey .bit
    ctx.canonicalFreshKey_fresh other
  have popped := Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey .bit
    ctx.canonicalFreshKey_fresh (bodyStep (model := model) left right output entered).1 other
  exact popped.trans (afterBranch.trans (afterCompare.trans pushed))

/-- The complete returned word contains the natural difference without modular wraparound. -/
theorem nativeSub_into_output_value (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (intoStep (model := model) left right output store).1.read (.storage output.toCStorageRef) =
      CShape.wordOfNat width ((store.read left).toNat - (store.read right).toNat) := by
  have natural := nativeSub_into_read_output (model := model) left right output store
  have fits : (store.read left).toNat - (store.read right).toNat < 2 ^ width :=
    (Nat.sub_le _ _).trans_lt (store.read left).toNat_lt
  cases actual : (intoStep (model := model) left right output store).1.read (.storage
    output.toCStorageRef) with
  | unsignedWord word =>
      apply congrArg CShape.Value.unsignedWord
      apply Fin.ext
      change word.val = ((store.read left).toNat - (store.read right).toNat) % 2 ^ width
      rw [Nat.mod_eq_of_lt fits]
      simpa only [actual, CShape.Value.toNat] using natural

/-- The actual complete store differs only by the one intended destination write. -/
theorem nativeSub_into_store (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (intoStep (model := model) left right output store).1 = store.write output
      (CShape.wordOfNat width ((store.read left).toNat - (store.read right).toNat)) := by
  apply Store.store_eq_write_of_read_frame
  · exact nativeSub_into_output_value (model := model) left right output store
  · intro shape other separate
    exact nativeSub_into_read_unchanged left right output (.storage other)
      (by simpa only [CInputRef.storageKeys, List.mem_singleton] using separate) store

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSub
