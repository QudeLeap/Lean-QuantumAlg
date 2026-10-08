/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Arithmetic

/-!
# Actual prepared operands for signed nearest division

The actual sign and magnitude writes feed the real wider-word operations.
The source width bounds prove that magnitude doubling and both resizes are
lossless. Every flag and original operand used later is read from the same
store after the intervening native writes.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem read_other {input output observed : CShape} (store : Store ctx)
    (op : ClassicalOp input output ctx ctx) (other : CWriteRef ctx observed)
    (different : op.outputRef.key ≠ other.key) :
    (store.applyOp op).read (writeInput other) = store.read (writeInput other) :=
  Store.read_applyOp_of_not_mem_storageKeys store op (writeInput other)
    (by simpa only [writeInput, CInputRef.storageKeys, List.mem_singleton] using different)

private theorem resize_read {sourceWidth targetWidth : Nat} (store : Store ctx)
    (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord targetWidth))
    (fits : (store.read input).toNat < CShape.wordModulus targetWidth) :
    ((store.applyOp (.wordResize sourceWidth targetWidth ctx input output)).read
      (writeInput output)).toNat = (store.read input).toNat := by
  change ((store.applyOp (.wordResize sourceWidth targetWidth ctx input output)).read
    (.storage (ClassicalOp.wordResize sourceWidth targetWidth ctx
      input output).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  exact ClassicalOp.eval_wordResize_exact sourceWidth targetWidth ctx input output
    (store.read input) fits

private theorem double_read (store : Store ctx) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (fits : 2 * (store.read input).toNat < CShape.wordModulus width) :
    ((store.applyOp (.wordUnary .shiftLeft width ctx input output)).read
      (writeInput output)).toNat =
      2 * (store.read input).toNat := by
  change ((store.applyOp (.wordUnary .shiftLeft width ctx input output)).read
    (.storage (ClassicalOp.wordUnary .shiftLeft width ctx
      input output).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  exact Nat.mod_eq_of_lt fits

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Reads outside the four actual prefix outputs survive preparation. -/
theorem prepare_callerFrame (refs : BodyRefs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoidsFlag : refs.negative.key ∉ other.storageKeys)
    (avoidsMagnitude : refs.magnitude.key ∉ other.storageKeys)
    (avoidsNumerator : refs.wideNumerator.key ∉ other.storageKeys)
    (avoidsDenominator : refs.wideDenominator.key ∉ other.storageKeys) :
    ((prepareStep (model := model) refs store).1).read other = store.read other := by
  unfold prepareStep
  dsimp only [BitWord.instructionStep]
  rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoidsDenominator,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoidsNumerator,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoidsNumerator]
  exact SignedWord.normalizeMagnitude_callerFrame refs.numerator refs.negative refs.magnitude
    store other avoidsFlag avoidsMagnitude

/-- Prepared words contain the exact doubled magnitude, original denominator and original sign. -/
theorem prepare_values (refs : BodyRefs ctx width) (separation : Separation refs)
    (store : Store ctx) (widthPositive : 0 < width) :
    (((prepareStep (model := model) refs store).1).read (writeInput refs.wideNumerator)).toNat =
        2 * rawMagnitude (store.read refs.numerator) ∧
      (((prepareStep (model := model) refs store).1).read (writeInput refs.wideDenominator)).toNat =
        (store.read refs.denominator).toNat ∧
      (((prepareStep (model := model) refs store).1).read (writeInput refs.negative)).toBool =
        rawIsNegative (store.read refs.numerator) := by
  let normalized := (normalizationStep (model := model) refs.numerator refs.negative
    refs.magnitude store).1
  let resized := normalized.applyOp (resizeMagnitudeOp refs)
  let doubled := resized.applyOp (doubleNumeratorOp refs)
  have magnitude : (normalized.read (writeInput refs.magnitude)).toNat =
      rawMagnitude (store.read refs.numerator) :=
    SignedWord.normalizeMagnitude_correct refs.numerator refs.negative refs.magnitude store
      separation.numeratorAvoidsNegative
  have sign : (normalized.read (writeInput refs.negative)).toBool =
      rawIsNegative (store.read refs.numerator) :=
    SignedWord.normalizeMagnitude_sign refs.numerator refs.negative refs.magnitude store
      separation.magnitudeNeNegative
  have denominatorNormalized : normalized.read refs.denominator = store.read refs.denominator :=
    SignedWord.normalizeMagnitude_callerFrame refs.numerator refs.negative refs.magnitude
      store refs.denominator separation.denominatorAvoidsNegative
      separation.denominatorAvoidsMagnitude
  have resizedValue : (resized.read (writeInput refs.wideNumerator)).toNat =
      rawMagnitude (store.read refs.numerator) := by
    have exactResize := resize_read normalized (writeInput refs.magnitude) refs.wideNumerator
      ((normalized.read (writeInput refs.magnitude)).toNat_lt.trans (wordModulus_lt_succ width))
    exact exactResize.trans magnitude
  have doubledValue : (doubled.read (writeInput refs.wideNumerator)).toNat =
      2 * rawMagnitude (store.read refs.numerator) := by
    have fits : 2 * (resized.read (writeInput refs.wideNumerator)).toNat <
        CShape.wordModulus (width + 1) := by
      rw [resizedValue]
      exact (Nat.le_add_right _ _).trans_lt
        (roundedDividend_fits widthPositive (store.read refs.numerator)
          (store.read refs.denominator))
    exact (double_read resized (writeInput refs.wideNumerator) refs.wideNumerator fits).trans
      (congrArg (2 * ·) resizedValue)
  have denominatorResized : resized.read refs.denominator = store.read refs.denominator :=
    (Store.read_applyOp_of_not_mem_storageKeys normalized (resizeMagnitudeOp refs)
      refs.denominator separation.denominatorAvoidsWideNumerator).trans denominatorNormalized
  have denominatorDoubled : doubled.read refs.denominator = store.read refs.denominator :=
    (Store.read_applyOp_of_not_mem_storageKeys resized (doubleNumeratorOp refs)
      refs.denominator separation.denominatorAvoidsWideNumerator).trans denominatorResized
  have signResized : (resized.read (writeInput refs.negative)).toBool =
      rawIsNegative (store.read refs.numerator) := by
    rw [read_other normalized (resizeMagnitudeOp refs) refs.negative
      (Ne.symm separation.negativeNeWideNumerator)]
    exact sign
  have signDoubled : (doubled.read (writeInput refs.negative)).toBool =
      rawIsNegative (store.read refs.numerator) := by
    rw [read_other resized (doubleNumeratorOp refs) refs.negative
      (Ne.symm separation.negativeNeWideNumerator)]
    exact signResized
  change (((doubled.applyOp (resizeDenominatorOp refs)).read
        (writeInput refs.wideNumerator)).toNat = _) ∧
    (((doubled.applyOp (resizeDenominatorOp refs)).read
        (writeInput refs.wideDenominator)).toNat = _) ∧
    (((doubled.applyOp (resizeDenominatorOp refs)).read (writeInput refs.negative)).toBool = _)
  refine ⟨?_, ?_, ?_⟩
  · rw [read_other doubled (resizeDenominatorOp refs) refs.wideNumerator
      (Ne.symm separation.wideNumeratorNeWideDenominator)]
    exact doubledValue
  · exact (resize_read doubled refs.denominator refs.wideDenominator
      ((doubled.read refs.denominator).toNat_lt.trans (wordModulus_lt_succ width))).trans
        (congrArg CShape.Value.toNat denominatorDoubled)
  · rw [read_other doubled (resizeDenominatorOp refs) refs.negative
      (Ne.symm separation.negativeNeWideDenominator)]
    exact signDoubled

end

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.RoundedDiv
