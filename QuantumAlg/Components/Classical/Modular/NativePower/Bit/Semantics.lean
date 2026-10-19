/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Bit.Execution

/-!
# Arithmetic of the actual exponent-bit fold

The accumulator's value follows the square-and-multiply recurrence of the
original operand reads. The separation conditions here concern only existing
structural references and are supplied by the enclosing fresh accumulator
placement. They never become additional assumptions on an algorithm's input.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

open Execution

noncomputable section

variable {width : Nat}

/-- One finite-word square and the base multiplication selected by the exponent bit. -/
def bitValue (base : CShape.Word width) (modulus : CShape.Word (width + 1))
    (accumulator : CShape.Word width) (bit : Bool) : CShape.Word width :=
  let squared := multiplyValue accumulator accumulator modulus
  if bit then multiplyValue squared base modulus else squared

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

private lemma bitStep_store (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bit : CInputRef ctx .bit)
    (store : Store ctx) :
    (bitStep (model := model) base modulus output bit store).1 =
      let squared := (scopedMultiplyStep (model := model) (wordRead output) (wordRead output)
        modulus output store).1
      if (squared.read bit).toBool then
        (scopedMultiplyStep (model := model) (wordRead output) base modulus output squared).1
      else squared := by
  change (multiplyChoiceStep (model := model) base modulus output
    (((scopedMultiplyStep (model := model) (wordRead output) (wordRead output)
      modulus output store).1).read bit)
    (scopedMultiplyStep (model := model) (wordRead output) (wordRead output)
      modulus output store).1).1 = _
  cases sampled : ((scopedMultiplyStep (model := model) (wordRead output) (wordRead output)
    modulus output store).1).read bit with
  | bit value =>
      dsimp only
      rw [sampled]
      cases value <;> rfl

/-- Every non-accumulator structural read is unchanged by either actual selected path. -/
lemma nativePower_bit_read_other (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bit : CInputRef ctx .bit)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    ((bitStep (model := model) base modulus output bit store).1).read other = store.read other := by
  have squared := nativePower_scopedMultiply_read_other (model := model)
    (wordRead output) (wordRead output) modulus output other separate store
  rw [bitStep_store]
  dsimp only
  split
  · exact (nativePower_scopedMultiply_read_other (model := model)
      (wordRead output) base modulus output other separate _).trans squared
  · exact squared

/-- The actual branch computes the recurrence on the original base, modulus and bit reads. -/
lemma nativePower_bit_read_output (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bit : CInputRef ctx .bit)
    (baseFree : output.key ∉ base.storageKeys)
    (modulusFree : output.key ∉ modulus.storageKeys)
    (bitFree : output.key ∉ bit.storageKeys) (store : Store ctx) :
    ((bitStep (model := model) base modulus output bit store).1).read (wordRead output) =
      bitValue (store.read base) (store.read modulus) (store.read (wordRead output))
        (store.read bit).toBool := by
  let squared := (scopedMultiplyStep (model := model) (wordRead output) (wordRead output)
    modulus output store).1
  have baseSame : squared.read base = store.read base :=
    nativePower_scopedMultiply_read_other (model := model) _ _ _ _ base baseFree store
  have modulusSame : squared.read modulus = store.read modulus :=
    nativePower_scopedMultiply_read_other (model := model) _ _ _ _ modulus modulusFree store
  have bitSame : squared.read bit = store.read bit :=
    nativePower_scopedMultiply_read_other (model := model) _ _ _ _ bit bitFree store
  have squaredResult : squared.read (wordRead output) =
      multiplyValue (store.read (wordRead output)) (store.read (wordRead output))
        (store.read modulus) :=
    nativePower_scopedMultiply_result (model := model) _ _ _ _ store
  rw [bitStep_store]
  change (if (squared.read bit).toBool then
    (scopedMultiplyStep (model := model) (wordRead output) base modulus output squared).1
      else squared).read
      (wordRead output) = _
  rw [bitSame]
  cases sampled : store.read bit with
  | bit value =>
      cases value
      · simpa only [CShape.Value.toBool, Bool.false_eq_true, if_false, bitValue]
          using squaredResult
      · simp only [CShape.Value.toBool, if_true, bitValue]
        rw [nativePower_scopedMultiply_result, squaredResult, baseSame, modulusSame]

/-- The complete finite fold preserves every structural read outside its accumulator. -/
lemma nativePower_fold_read_other (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bits : List (CInputRef ctx .bit))
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    ((foldStep (model := model) base modulus output bits store).1).read other =
      store.read other := by
  induction bits generalizing store with
  | nil => rfl
  | cons bit rest ih =>
      change ((foldStep (model := model) base modulus output rest
        (bitStep (model := model) base modulus output bit store).1).1).read
        other = _
      rw [ih]
      exact nativePower_bit_read_other (model := model) base modulus output bit other separate store

/-- Same-store finite composition yields exactly the mathematical recurrence of its actual bits. -/
lemma nativePower_fold_read_output (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bits : List (CInputRef ctx .bit))
    (baseFree : output.key ∉ base.storageKeys)
    (modulusFree : output.key ∉ modulus.storageKeys)
    (bitsFree : ∀ bit ∈ bits, output.key ∉ bit.storageKeys) (store : Store ctx) :
    ((foldStep (model := model) base modulus output bits store).1).read (wordRead output) =
      (bits.map (fun bit => (store.read bit).toBool)).foldl
        (bitValue (store.read base) (store.read modulus)) (store.read (wordRead output)) := by
  induction bits generalizing store with
  | nil => rfl
  | cons bit rest ih =>
      have firstFree := bitsFree bit (.head rest)
      have laterFree : ∀ other ∈ rest, output.key ∉ other.storageKeys :=
        fun other present => bitsFree other (.tail bit present)
      have remaining : rest.map (fun other =>
          (((bitStep (model := model) base modulus output bit store).1).read other).toBool) =
          rest.map (fun other => (store.read other).toBool) := by
        apply List.map_congr_left
        intro other present
        exact congrArg CShape.Value.toBool
          (nativePower_bit_read_other (model := model) base modulus output bit other
            (laterFree other present) store)
      change ((foldStep (model := model) base modulus output rest
        (bitStep (model := model) base modulus output bit store).1).1).read
        (wordRead output) = _
      rw [ih laterFree, remaining,
        nativePower_bit_read_other (model := model) base modulus output bit base baseFree store,
        nativePower_bit_read_other (model := model) base modulus output bit modulus
          modulusFree store,
        nativePower_bit_read_output (model := model) base modulus output bit
          baseFree modulusFree firstFree store]
      rfl

end

end QuantumAlg.ClassicalRoutines.Modular.NativePower
