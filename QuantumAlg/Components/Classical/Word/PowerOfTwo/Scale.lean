/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Word.PowerOfTwo.Resources

/-!
# Actual native scaling of an original word by a power of two

The actual source word is resized into its supplied destination and shifted
left the prescribed number of times. The complete original unsigned value is
scaled exactly when the source width plus shift count fits the output width.
No input/output separation or initial destination value is required.
-/

namespace QuantumAlg.ClassicalRoutines.Word.PowerOfTwo.Scale

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {sourceWidth width : Nat}

/-- Actual native resize from the original structural source into the supplied destination. -/
def resizeOp (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord sourceWidth) (.unsignedWord width) ctx ctx :=
  .wordResize sourceWidth width ctx input output

/-- The actual original source resize precedes the prescribed native left shifts. -/
def into (count : Nat) (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (resizeOp input output)) (PowerOfTwo.shiftInto count output)

/-- Complete actual scaled store and chronological resize-and-shift path. -/
def step (count : Nat) (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (into count input output).Path :=
  let shifted := PowerOfTwo.shiftStep count output (store.applyOp (resizeOp input output))
  (shifted.1, ((), shifted.2))

/-- Actual native scaling preserves every original state block and quantum-reference correlation. -/
theorem into_execute (count : Nat) (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into count input output).execute Reference state = state.mapClassical (fun entry =>
      ((step count input output entry.1).1, (entry.2, (step count input output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (resizeOp input output))
    (PowerOfTwo.shiftInto count output) (fun store => (store.applyOp (resizeOp input output), ()))
    (PowerOfTwo.shiftStep count output) (by
      intro Reference History _ state
      refine (Circuit.execute_classical_mapClassical (resizeOp input output)
        Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) (PowerOfTwo.shiftInto_execute count output)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Native resizing materializes the original source value modulo the destination width. -/
theorem resize_read (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((store.applyOp (resizeOp input output)).read (.storage output.toCStorageRef)).toNat =
      (store.read input).toNat % 2 ^ width := by
  simp only [Store.applyOp, resizeOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval_wordResize_toNat]
  rfl

/-- The actual resize-and-shift sequence scales the original source modulo the output width. -/
theorem into_read_mod (count : Nat) (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((step count input output store).1.read (.storage output.toCStorageRef)).toNat =
      ((store.read input).toNat * 2 ^ count) % 2 ^ width := by
  change ((PowerOfTwo.shiftStore count output (store.applyOp (resizeOp input output))).read
    (.storage output.toCStorageRef)).toNat = _
  rw [PowerOfTwo.shiftInto_read, resize_read]
  exact PowerOfTwo.mod_mul _ _ _

/-- The original source width and the requested shift count give a sufficient exact output width. -/
theorem scaled_lt_capacity (count : Nat) (input : CInputRef ctx (.unsignedWord sourceWidth))
    (store : Store ctx) (capacity : sourceWidth + count ≤ width) :
    (store.read input).toNat * 2 ^ count < 2 ^ width := by
  have sourceFits : (store.read input).toNat < 2 ^ sourceWidth := (store.read input).toNat_lt
  have productFits : (store.read input).toNat * 2 ^ count < 2 ^ (sourceWidth + count) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right sourceFits (by positivity)
  have widthFits : 2 ^ (sourceWidth + count) ≤ 2 ^ width := by
    gcongr
    omega
  exact productFits.trans_le widthFits

/-- The actual native result is the exact scaled original input whenever its full width fits. -/
theorem into_read (count : Nat) (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (capacity : sourceWidth + count ≤ width) :
    ((step count input output store).1.read (.storage output.toCStorageRef)).toNat =
      (store.read input).toNat * 2 ^ count := by
  rw [into_read_mod, Nat.mod_eq_of_lt (scaled_lt_capacity count input store capacity)]

/-- Every actual read outside the supplied destination survives the complete native scale. -/
theorem into_callerFrame (count : Nat) (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : output.key ∉ other.storageKeys) :
    (step count input output store).1.read other = store.read other := by
  change (PowerOfTwo.shiftStore count output (store.applyOp (resizeOp input output))).read other = _
  rw [PowerOfTwo.shiftInto_callerFrame _ _ _ other avoids]
  exact Store.read_applyOp_of_not_mem_storageKeys store (resizeOp input output) other avoids

end

end QuantumAlg.ClassicalRoutines.Word.PowerOfTwo.Scale
