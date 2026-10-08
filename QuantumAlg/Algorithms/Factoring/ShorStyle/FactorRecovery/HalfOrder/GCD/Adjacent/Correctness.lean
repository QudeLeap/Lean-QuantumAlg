/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Adjacent.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Adjacent.Arithmetic
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Actual written adjacent values for the factor GCDs

The numerical result is proved from the real first read, widening, native
arithmetic and selected underflow arm. No alias condition is needed between
the original operand and destination: the operand is consumed before that
destination is changed. Every other structural read outside the written key
is preserved by the same actual instructions.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeAdjacentWord

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {width : Nat}

private theorem trim_read_toNat (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (store : Store ctx) :
    ((trimStep (model := model) output store).1.read (read output)).toNat =
      if (store.read (highBit output)).toBool then 0 else (store.read (read output)).toNat := by
  simp only [trimStep]
  cases store.read (highBit output) with
  | bit value =>
      cases value
      · simp only [trimArmStep, CShape.Value.toBool, Bool.false_eq_true,
          if_false]
      · simp only [trimArmStep, BitWord.instructionStep, CShape.Value.toBool, if_true]
        exact (congrArg CShape.Value.toNat
          (Store.read_applyOp_output store (clearOp output))).trans
          (selfXor_toNat (store.read (read output)))

/-- The real adjacent program returns exactly the original natural successor or predecessor. -/
theorem result_toNat (successor : Bool) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    ((step (model := model) successor input output store).1.read (read output)).toNat =
      if successor then (store.read input).toNat + 1 else (store.read input).toNat - 1 := by
  let resized := store.applyOp (resizeOp input output)
  have resizedRead : resized.read (read output) =
      CShape.wordResize (width + 1) (store.read input) :=
    Store.read_applyOp_output store (resizeOp input output)
  cases successor
  · let decremented := resized.applyOp (adjacentOp false output)
    have decrementedRead : decremented.read (read output) =
        Resource.WordUnaryOpcode.eval .decrement (width + 1)
          (CShape.wordResize (width + 1) (store.read input)) :=
      (Store.read_applyOp_output resized (adjacentOp false output)).trans
        (congrArg (Resource.WordUnaryOpcode.eval .decrement (width + 1)) resizedRead)
    have high : (decremented.read (highBit output)).toBool =
        decide ((store.read input).toNat = 0) := by
      change ((decremented.read (read output)).wordBitGet 0).toBool = _
      exact (congrArg (fun value : CShape.Word (width + 1) =>
        (value.wordBitGet 0).toBool) decrementedRead).trans
        (decrement_highBit (store.read input))
    have number := (congrArg CShape.Value.toNat decrementedRead).trans
      (decrement_toNat (store.read input))
    change ((trimStep (model := model) output decremented).1.read (read output)).toNat =
      (store.read input).toNat - 1
    rw [trim_read_toNat, high, number]
    by_cases zero : (store.read input).toNat = 0
    · simp only [zero, decide_true, if_true, Nat.zero_sub]
    · simp only [zero, decide_false, Bool.false_eq_true, if_false]
  · change ((resized.applyOp (adjacentOp true output)).read (read output)).toNat =
      (store.read input).toNat + 1
    exact (congrArg CShape.Value.toNat
      ((Store.read_applyOp_output resized (adjacentOp true output)).trans
        (congrArg (Resource.WordUnaryOpcode.eval .increment (width + 1)) resizedRead))).trans
      (increment_toNat (store.read input))

private theorem trim_read_other (output : CWriteRef ctx (.unsignedWord (width + 1)))
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (trimStep (model := model) output store).1.read other = store.read other := by
  simp only [trimStep]
  cases store.read (highBit output) with
  | bit value =>
      cases value
      · rfl
      · change (store.applyOp (clearOp output)).read other = store.read other
        exact Store.read_applyOp_of_not_mem_storageKeys store (clearOp output) other separate

/-- Every other original structural operand retains its value through the genuine adjacent code. -/
theorem read_other (successor : Bool) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1))) {shape : CShape}
    (other : CInputRef ctx shape) (separate : output.key ∉ other.storageKeys)
    (store : Store ctx) :
    (step (model := model) successor input output store).1.read other = store.read other := by
  have resized := Store.read_applyOp_of_not_mem_storageKeys store
    (resizeOp input output) other separate
  cases successor
  · exact (trim_read_other (model := model) output other separate
      ((store.applyOp (resizeOp input output)).applyOp (adjacentOp false output))).trans
      ((Store.read_applyOp_of_not_mem_storageKeys (store.applyOp (resizeOp input output))
        (adjacentOp false output) other separate).trans resized)
  · exact (Store.read_applyOp_of_not_mem_storageKeys (store.applyOp (resizeOp input output))
      (adjacentOp true output) other separate).trans resized

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeAdjacentWord
