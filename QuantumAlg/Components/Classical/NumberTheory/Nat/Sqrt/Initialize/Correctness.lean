/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Initialize.Program

/-!
# Exact initialized search cells and complete caller frame

Positive input width is the original arithmetic domain. The initialization
has no assumptions on the incoming work cells or future output value.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt

open Execution
open IntegerSqrt (writeInput)

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {inputWidth : Nat}

/-- Exact prepared input and interval, unchanged output, and all other caller reads. -/
structure InitOutcome (refs : Refs ctx inputWidth) (before after : Store ctx) : Prop where
  wide : (after.read (wideInput refs)).toNat = (before.read refs.input).toNat
  root : (after.read (writeInput refs.round.root)).toNat = 0
  half : (after.read (writeInput refs.round.half)).toNat = 2 ^ (inputWidth - 1)
  output : after.read (writeInput refs.output) = before.read (writeInput refs.output)
  callerFrame : CallerFrame refs before after

private theorem initializeClear_value
    (output : CWriteRef ctx (.unsignedWord (workWidth inputWidth))) (store : Store ctx) :
    ((store.applyOp (initializeClearOp output)).read (writeInput output)).toNat = 0 := by
  change ((store.applyOp (initializeClearOp output)).read
    (.storage (initializeClearOp output).outputRef.toCStorageRef)).toNat = 0
  rw [Store.read_applyOp_output]
  change (CShape.wordBitXor (workWidth inputWidth) (store.read (writeInput output))
    (store.read (writeInput output))).toNat = 0
  simp [CShape.wordBitXor, CShape.wordOfNat_val]

/-- A shift loop frames every complete caller read outside the half cell. -/
theorem shiftHalfLoopStep_callerFrame (refs : Refs ctx inputWidth) (count : Nat)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (separate : refs.round.half.key ∉ other.storageKeys) :
    (shiftHalfLoopStep refs count store).1.read other = store.read other := by
  change ((fun before => before.applyOp (shiftHalfOp refs))^[count] store).read other = _
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply']
      exact (Store.read_applyOp_of_not_mem_storageKeys _ (shiftHalfOp refs) other separate).trans ih

/-- A fixed shift loop advances a known power of two without modular wrapping. -/
theorem shiftHalfLoopStep_value (refs : Refs ctx inputWidth) (count start : Nat)
    (range : start + count < workWidth inputWidth) (store : Store ctx)
    (initial : (store.read (writeInput refs.round.half)).toNat = 2 ^ start) :
    ((shiftHalfLoopStep refs count store).1.read (writeInput refs.round.half)).toNat =
      2 ^ (start + count) := by
  change (((fun before => before.applyOp (shiftHalfOp refs))^[count] store).read
    (writeInput refs.round.half)).toNat = _
  induction count with
  | zero => simpa only [Function.iterate_zero_apply, Nat.add_zero] using initial
  | succ count ih =>
      have prefixValue := ih (by omega)
      have doubledFits :
          2 * (((fun before => before.applyOp (shiftHalfOp refs))^[count] store).read
            (writeInput refs.round.half)).toNat < CShape.wordModulus (workWidth inputWidth) := by
        rw [prefixValue]
        change 2 * 2 ^ (start + count) < 2 ^ workWidth inputWidth
        calc
          2 * 2 ^ (start + count) = 2 ^ (start + count + 1) := by
            rw [pow_succ]
            ac_rfl
          _ < 2 ^ workWidth inputWidth :=
            Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
      rw [Function.iterate_succ_apply']
      change (((_ : Store ctx).applyOp (shiftHalfOp refs)).read
        (.storage (shiftHalfOp refs).outputRef.toCStorageRef)).toNat = _
      rw [Store.read_applyOp_output]
      change (CShape.wordShiftLeft (workWidth inputWidth)
        (((fun before => before.applyOp (shiftHalfOp refs))^[count] store).read
          (writeInput refs.round.half))).toNat = _
      rw [CShape.wordShiftLeft, CShape.wordOfNat_val, Nat.mod_eq_of_lt doubledFits, prefixValue]
      rw [Nat.add_succ, pow_succ]
      ac_rfl

/-- Initialization preserves every caller read outside the three actual write keys. -/
theorem initializeInto_callerFrame (refs : Refs ctx inputWidth) (store : Store ctx) :
    CallerFrame refs store (initializeStep refs store).1 := by
  intro shape other avoidsWide avoidsRoot avoidsHalf
  change (shiftHalfLoopStep refs (inputWidth - 1) (initializeSeed refs store)).1.read other = _
  rw [shiftHalfLoopStep_callerFrame refs _ _ other avoidsHalf]
  unfold initializeSeed
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (initializeIncrementOp refs) other avoidsHalf,
    Store.read_applyOp_of_not_mem_storageKeys _ (initializeClearOp refs.round.half)
      other avoidsHalf,
    Store.read_applyOp_of_not_mem_storageKeys _ (initializeClearOp refs.round.root)
      other avoidsRoot,
    Store.read_applyOp_of_not_mem_storageKeys _ (initializeResizeOp refs) other avoidsWide]

private theorem initializeSeed_wide (refs : Refs ctx inputWidth) (separation : Separation refs)
    (store : Store ctx) :
    ((initializeSeed refs store).read (wideInput refs)).toNat = (store.read refs.input).toNat := by
  unfold initializeSeed
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (initializeIncrementOp refs)
      (wideInput refs) separation.wideInputAvoidsHalf,
    Store.read_applyOp_of_not_mem_storageKeys _ (initializeClearOp refs.round.half)
      (wideInput refs) separation.wideInputAvoidsHalf,
    Store.read_applyOp_of_not_mem_storageKeys _ (initializeClearOp refs.round.root)
      (wideInput refs) separation.wideInputAvoidsRoot]
  change ((store.applyOp (initializeResizeOp refs)).read
    (.storage (initializeResizeOp refs).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  apply ClassicalOp.eval_wordResize_exact
  calc
    (store.read refs.input).toNat < CShape.wordModulus inputWidth :=
      (store.read refs.input).toNat_lt
    _ ≤ CShape.wordModulus (workWidth inputWidth + workWidth inputWidth) := by
      change 2 ^ inputWidth ≤ 2 ^ (inputWidth + inputWidth)
      exact Nat.pow_le_pow_right (by omega) (by omega)

private theorem initializeSeed_root (refs : Refs ctx inputWidth) (separation : Separation refs)
    (store : Store ctx) :
    ((initializeSeed refs store).read (writeInput refs.round.root)).toNat = 0 := by
  unfold initializeSeed
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (initializeIncrementOp refs)
      (writeInput refs.round.root) separation.rootAvoidsHalf,
    Store.read_applyOp_of_not_mem_storageKeys _ (initializeClearOp refs.round.half)
      (writeInput refs.round.root) separation.rootAvoidsHalf]
  exact initializeClear_value refs.round.root _

private theorem initializeSeed_half (refs : Refs ctx inputWidth) (positive : 0 < inputWidth)
    (store : Store ctx) :
    ((initializeSeed refs store).read (writeInput refs.round.half)).toNat = 1 := by
  unfold initializeSeed
  change (((_ : Store ctx).applyOp (initializeIncrementOp refs)).read
    (.storage (initializeIncrementOp refs).outputRef.toCStorageRef)).toNat = 1
  rw [Store.read_applyOp_output]
  change (CShape.wordOfNat (workWidth inputWidth)
    (((_ : Store ctx).applyOp (initializeClearOp refs.round.half)).read
      (writeInput refs.round.half)).toNat.succ).toNat = 1
  rw [initializeClear_value, CShape.wordOfNat_val]
  exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt positive))

/-- Actual initialization establishes the original interval with arbitrary incoming work values. -/
theorem initializeInto_correct (refs : Refs ctx inputWidth) (separation : Separation refs)
    (positive : 0 < inputWidth) (store : Store ctx) :
    InitOutcome refs store (initializeStep refs store).1 := by
  have frame : CallerFrame refs store (initializeStep refs store).1 :=
    initializeInto_callerFrame refs store
  refine ⟨?_, ?_, ?_, frame (writeInput refs.output) separation.outputAvoidsWideInput
    separation.outputAvoidsRoot separation.outputAvoidsHalf, frame⟩
  · change ((shiftHalfLoopStep refs (inputWidth - 1) (initializeSeed refs store)).1.read
      (wideInput refs)).toNat = _
    rw [shiftHalfLoopStep_callerFrame refs _ _ (wideInput refs) separation.wideInputAvoidsHalf]
    exact initializeSeed_wide refs separation store
  · change ((shiftHalfLoopStep refs (inputWidth - 1) (initializeSeed refs store)).1.read
      (writeInput refs.round.root)).toNat = 0
    rw [shiftHalfLoopStep_callerFrame refs _ _ (writeInput refs.round.root)
      separation.rootAvoidsHalf]
    exact initializeSeed_root refs separation store
  · have shifts := shiftHalfLoopStep_value refs (inputWidth - 1) 0
      (by unfold workWidth; omega) (initializeSeed refs store)
      (by simpa only [pow_zero] using initializeSeed_half refs positive store)
    simpa only [initializeStep, Nat.zero_add] using shifts

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt
