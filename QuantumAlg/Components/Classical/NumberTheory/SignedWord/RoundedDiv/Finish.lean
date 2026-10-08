/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Preparation

/-!
# Actual quotient and sign restoration

The quotient is read from the product cell written by the native division.
Its resize and stored-sign restoration represent the signed result modulo the
output width, including a zero quotient in the negative branch.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem unary_read (opcode : Resource.WordUnaryOpcode) (store : Store ctx)
    (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    (store.applyOp (.wordUnary opcode width ctx input output)).read (writeInput output) =
      opcode.eval width (store.read input) := by
  exact Store.read_applyOp_output store (.wordUnary opcode width ctx input output)

/-- The native division's stored quotient is exactly the division of its actual inputs. -/
theorem divide_quotient (refs : BodyRefs ctx width) (store : Store ctx) :
    ((store.applyOp (divideOp refs)).read (.first (writeInput refs.division))).toNat =
      (store.read (writeInput refs.wideNumerator)).toNat /
        (store.read (writeInput refs.wideDenominator)).toNat := by
  change (((store.applyOp (divideOp refs)).read
    (.storage (divideOp refs).outputRef.toCStorageRef)).first).toNat = _
  rw [Store.read_applyOp_output]
  exact ClassicalOp.eval_divRem_quotient_exact (width + 1) (width + 1) ctx
    (divideOp refs).inputRef refs.division (store.read (divideOp refs).inputRef)

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

private theorem restore_represents (refs : BodyRefs ctx width)
    (flag : CShape.Value .bit) (store : Store ctx) (value : Int)
    (represents : RawSignedRepresents (store.read (writeInput refs.output)) value) :
    RawSignedRepresents ((restoreStep (model := model) refs flag store).1.read (writeInput
      refs.output))
      (if flag.toBool then -value else value) := by
  cases flag with
  | bit flag =>
      cases flag
      · exact represents
      · change RawSignedRepresents
          (((store.applyOp (complementOutputOp refs)).applyOp (incrementOutputOp refs)).read
            (writeInput refs.output)) (-value)
        unfold incrementOutputOp complementOutputOp
        rw [unary_read .increment, unary_read .complement]
        exact rawSignedWordRepresents_negate _ value represents

private theorem restore_frame (refs : BodyRefs ctx width)
    (flag : CShape.Value .bit) (store : Store ctx) {shape : CShape}
    (other : CInputRef ctx shape) (avoids : refs.output.key ∉ other.storageKeys) :
    ((restoreStep (model := model) refs flag store).1).read other = store.read other := by
  cases flag with
  | bit flag =>
      cases flag
      · rfl
      · change (((store.applyOp (complementOutputOp refs)).applyOp
          (incrementOutputOp refs)).read other) = _
        rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoids,
          Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoids]

/-- Only the actual quotient output cell is changed by the final stage. -/
theorem finish_callerFrame (refs : BodyRefs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : refs.output.key ∉ other.storageKeys) :
    ((finishStep (model := model) refs store).1).read other = store.read other := by
  unfold finishStep
  dsimp only [BitWord.instructionStep]
  rw [restore_frame _ _ _ _ avoids, Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoids]

/-- The retained sign selects the signed value represented by the resized real quotient. -/
theorem finish_represents (refs : BodyRefs ctx width) (store : Store ctx)
    (separate : refs.output.key ≠ refs.negative.key) :
    RawSignedRepresents ((finishStep (model := model) refs store).1.read (writeInput refs.output))
      (if (store.read (writeInput refs.negative)).toBool then
        -(((store.read (.first (writeInput refs.division))).toNat : Nat) : Int)
      else (((store.read (.first (writeInput refs.division))).toNat : Nat) : Int)) := by
  let resized := store.applyOp (resizeQuotientOp refs)
  have resizedValue : RawSignedRepresents (resized.read (writeInput refs.output))
      ((store.read (.first (writeInput refs.division))).toNat : Int) := by
    change RawSignedRepresents ((store.applyOp (resizeQuotientOp refs)).read
      (.storage (resizeQuotientOp refs).outputRef.toCStorageRef)) _
    rw [Store.read_applyOp_output]
    exact rawSignedWordRepresents_wordResize _
  have restored := restore_represents (model := model) refs (resized.read (writeInput
    refs.negative))
    resized _ resizedValue
  rw [read_other store (resizeQuotientOp refs) refs.negative separate] at restored
  change RawSignedRepresents
    ((restoreStep (model := model) refs (resized.read (writeInput refs.negative)) resized).1.read
      (writeInput refs.output)) _
  rw [read_other store (resizeQuotientOp refs) refs.negative separate]
  exact restored

end

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv
