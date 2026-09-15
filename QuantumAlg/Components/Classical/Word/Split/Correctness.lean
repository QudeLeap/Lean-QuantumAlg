/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Word.Split
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Exact actual unsigned word split values and caller frame

The working word is divided by the exact low-width power of two. The low
output retains the original remainder, and the high output is the exact
quotient because the original combined-width value supplies its capacity.
-/

namespace QuantumAlg.ClassicalRoutines.Word.Split

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width highWidth lowWidth : Nat}

/-- A native shift preserves every read outside its actual working word. -/
theorem shift_frame (work : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : work.key ∉ other.storageKeys) :
    (store.applyOp (shiftOp work)).read other = store.read other :=
  Store.read_applyOp_of_not_mem_storageKeys store (shiftOp work) other avoids

/-- One actual native right shift is exact division by two, even at word width zero. -/
theorem shift_read (work : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((store.applyOp (shiftOp work)).read (.storage work.toCStorageRef)).toNat =
      (store.read (.storage work.toCStorageRef)).toNat / 2 := by
  simp only [Store.applyOp, shiftOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval_wordUnary]
  cases store.read (.storage work.toCStorageRef) with
  | unsignedWord word =>
    change (CShape.wordOfNat width (word.val / 2)).toNat = word.val / 2
    rw [CShape.wordOfNat_val]
    change word.val / 2 % 2 ^ width = word.val / 2
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self word.val 2) word.isLt)

/-- Any finite sequence of native shifts retains the full nonworking caller frame. -/
theorem shiftInto_callerFrame (count : Nat) (work : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : work.key ∉ other.storageKeys) :
    (shiftStore count work store).read other = store.read other := by
  change ((fun current => current.applyOp (shiftOp work))^[count] store).read other = _
  induction count generalizing store with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply, ih, shift_frame work store other avoids]

/-- The actual repeated shifts divide the original working word by precisely two to the count. -/
theorem shiftInto_read (count : Nat) (work : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    ((shiftStore count work store).read (.storage work.toCStorageRef)).toNat =
      (store.read (.storage work.toCStorageRef)).toNat / 2 ^ count := by
  change (((fun current => current.applyOp (shiftOp work))^[count] store).read
    (.storage work.toCStorageRef)).toNat = _
  induction count generalizing store with
  | zero => simp
  | succ count ih =>
    rw [Function.iterate_succ_apply, ih, shift_read, Nat.div_div_eq_div_mul, pow_succ]
    rw [Nat.mul_comm 2]

private theorem resize_read {sourceWidth targetWidth : Nat}
    (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord targetWidth)) (store : Store ctx) :
    ((store.applyOp (.wordResize sourceWidth targetWidth ctx input output)).read
      (.storage output.toCStorageRef)).toNat = (store.read input).toNat %
        CShape.wordModulus targetWidth := by
  simp only [Store.applyOp, ClassicalOp.outputRef, Store.read_write_same, ClassicalOp.inputRef,
    ClassicalOp.eval_wordResize_toNat]

/-- Actual low-width extraction reads the original work word modulo its low-width capacity. -/
theorem low_read (refs : Refs ctx highWidth lowWidth) (store : Store ctx) :
    ((store.applyOp (lowOp refs)).read (.storage refs.low.toCStorageRef)).toNat =
      (store.read (.storage refs.work.toCStorageRef)).toNat % CShape.wordModulus lowWidth :=
  resize_read _ _ store

/-- Actual high-width extraction reads the shifted work word modulo its high-width capacity. -/
theorem high_read (refs : Refs ctx highWidth lowWidth) (store : Store ctx) :
    ((store.applyOp (highOp refs)).read (.storage refs.high.toCStorageRef)).toNat =
      (store.read (.storage refs.work.toCStorageRef)).toNat % CShape.wordModulus highWidth :=
  resize_read _ _ store

private theorem low_work (refs : Refs ctx highWidth lowWidth) (separation : Separation refs)
    (store : Store ctx) :
    (store.applyOp (lowOp refs)).read (.storage refs.work.toCStorageRef) =
      store.read (.storage refs.work.toCStorageRef) :=
  Store.read_applyOp_of_not_mem_storageKeys store (lowOp refs) _
    (by simpa only [lowOp, ClassicalOp.outputRef, CInputRef.storageKeys,
      List.mem_singleton] using separation.workNeLow.symm)

/-- The actual destructive working word ends at the exact original high quotient. -/
theorem splitInto_work (refs : Refs ctx highWidth lowWidth) (separation : Separation refs)
    (store : Store ctx) :
    ((splitStep refs store).1.read (.storage refs.work.toCStorageRef)).toNat =
      (store.read (.storage refs.work.toCStorageRef)).toNat / 2 ^ lowWidth := by
  change (((shiftStore lowWidth refs.work (store.applyOp (lowOp refs))).applyOp
    (highOp refs)).read (.storage refs.work.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (highOp refs) _
    (by simpa only [highOp, ClassicalOp.outputRef, CInputRef.storageKeys,
      List.mem_singleton] using separation.workNeHigh.symm),
    shiftInto_read, low_work refs separation store]

/-- The actual low output retains the original remainder through all later writes. -/
theorem splitInto_low (refs : Refs ctx highWidth lowWidth) (separation : Separation refs)
    (store : Store ctx) :
    ((splitStep refs store).1.read (.storage refs.low.toCStorageRef)).toNat =
      (store.read (.storage refs.work.toCStorageRef)).toNat % 2 ^ lowWidth := by
  change (((shiftStore lowWidth refs.work (store.applyOp (lowOp refs))).applyOp
    (highOp refs)).read (.storage refs.low.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (highOp refs) _
    (by simpa only [highOp, ClassicalOp.outputRef, CInputRef.storageKeys,
      List.mem_singleton] using separation.highNeLow),
    shiftInto_callerFrame lowWidth refs.work _ _
      (by simpa only [CInputRef.storageKeys, List.mem_singleton] using separation.workNeLow),
    low_read]
  rfl

/-- The original combined-width capacity makes the actual high output the exact quotient. -/
theorem splitInto_high (refs : Refs ctx highWidth lowWidth) (separation : Separation refs)
    (store : Store ctx) :
    ((splitStep refs store).1.read (.storage refs.high.toCStorageRef)).toNat =
      (store.read (.storage refs.work.toCStorageRef)).toNat / 2 ^ lowWidth := by
  have bound := CShape.Value.toNat_lt (store.read (.storage refs.work.toCStorageRef))
  have quotientFits : (store.read (.storage refs.work.toCStorageRef)).toNat / 2 ^ lowWidth <
      CShape.wordModulus highWidth := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).2
    simpa only [CShape.wordModulus, pow_add] using bound
  change (((shiftStore lowWidth refs.work (store.applyOp (lowOp refs))).applyOp
    (highOp refs)).read (.storage refs.high.toCStorageRef)).toNat = _
  rw [high_read, shiftInto_read, low_work refs separation store, Nat.mod_eq_of_lt quotientFits]

/-- Every actual read outside the three supplied write cells is retained exactly. -/
theorem splitInto_callerFrame (refs : Refs ctx highWidth lowWidth) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (work : refs.work.key ∉ other.storageKeys) (high : refs.high.key ∉ other.storageKeys)
    (low : refs.low.key ∉ other.storageKeys) :
    (splitStep refs store).1.read other = store.read other := by
  change ((shiftStore lowWidth refs.work (store.applyOp (lowOp refs))).applyOp
    (highOp refs)).read other = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (highOp refs) other high,
    shiftInto_callerFrame _ _ _ other work,
    Store.read_applyOp_of_not_mem_storageKeys store (lowOp refs) other low]

end

end QuantumAlg.ClassicalRoutines.Word.Split
