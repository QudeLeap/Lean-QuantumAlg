/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Correction
import all QuantumAlg.Components.Classical.Modular.Reduce.Native.Semantics
import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Correction.Model

/-!
# Exact actual negative signed-remainder correction

The four real operations preserve the complete quantum-reference state and
all caller reads outside the result. The second division handles a zero
remainder exactly, including a modulus equal to the original word capacity.
The result may alias an original operand; the widened scratch is internal.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native

open Execution Modular.Reduce.Native ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Exact fixed-width result of the original widened subtraction and second reduction. -/
def negativeCorrectionValue (remainder : CShape.Word width)
    (modulus : CShape.Word (width + 1)) : CShape.Word width :=
  reductionValue (CShape.wordSub (width + 1) modulus (CShape.wordResize (width + 1) remainder))
    modulus

/-- All four actual operations retain complete quantum-reference blocks and original histories. -/
theorem correctionBody_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (extended : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (correctionBody (model := model) remainder modulus extended output).execute Reference state =
      state.mapClassical (fun entry =>
        ((correctionBodyStep (model := model) remainder modulus extended output entry.1).1,
          (entry.2.1, (entry.2.2, (correctionBodyStep (model := model) remainder modulus extended
            output entry.1).2)))) := by
  simp only [correctionBody, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    reduceWord_execute, State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Internal scratch separation suffices for the exact finite word, without a range promise. -/
theorem correctionBody_value {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (extended : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (modulusFree : extended.key ∉ modulus.storageKeys) :
    (correctionBodyStep (model := model) remainder modulus extended output store).1.read
      (reductionRead output) =
      negativeCorrectionValue (store.read remainder) (store.read modulus) := by
  let resized := store.applyOp (correctionResizeOp remainder extended)
  let subtracted := resized.applyOp (correctionSubtractOp modulus extended)
  have resizedValue : resized.read (reductionRead extended) =
      CShape.wordResize (width + 1) (store.read remainder) :=
    Store.read_applyOp_output store (correctionResizeOp remainder extended)
  have resizedModulus : resized.read modulus = store.read modulus :=
    Store.read_applyOp_of_not_mem_storageKeys _ (correctionResizeOp remainder extended)
      modulus modulusFree
  have subtractedValue : subtracted.read (reductionRead extended) =
      CShape.wordSub (width + 1) (resized.read modulus) (resized.read (reductionRead extended)) :=
    Store.read_applyOp_output resized (correctionSubtractOp modulus extended)
  have subtractedModulus : subtracted.read modulus = store.read modulus :=
    (Store.read_applyOp_of_not_mem_storageKeys _ (correctionSubtractOp modulus extended)
      modulus modulusFree).trans resizedModulus
  change (reduceWordStep (model := model) (reductionRead extended) modulus output subtracted).1.read
    (reductionRead output) = _
  rw [reduceWord_value, subtractedValue, subtractedModulus, resizedModulus, resizedValue]
  rfl

/-- Every structural read outside scratch and result keys survives all four operations. -/
theorem correctionBody_read_other {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (extended : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) {shape : CShape} (other : CInputRef ctx shape)
    (extendedFree : extended.key ∉ other.storageKeys) (outputFree : output.key ∉ other.storageKeys)
    (store : Store ctx) :
    (correctionBodyStep (model := model) remainder modulus extended output store).1.read other =
      store.read other := by
  change (reduceWordStep (model := model) (reductionRead extended) modulus output
    ((store.applyOp (correctionResizeOp remainder extended)).applyOp
      (correctionSubtractOp modulus extended))).1.read other = _
  rw [reduceWord_read_other _ _ _ other outputFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (correctionSubtractOp modulus extended)
      other extendedFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (correctionResizeOp remainder extended)
      other extendedFree]

/-- Actual widened-word entry and both matching scratch releases preserve full reference data. -/
theorem withNegativeCorrection_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (withNegativeCorrection (model := model) remainder modulus output).execute Reference state =
      state.mapClassical (fun entry =>
        ((withNegativeCorrectionStep (model := model) remainder modulus output entry.1).1,
          (entry.2.1, (entry.2.2, (withNegativeCorrectionStep (model := model) remainder modulus
            output entry.1).2)))) := by
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh (correctionPlaced (model := model) remainder modulus output)
    (fun before =>
      let result := correctionBodyStep (model := model) (underCorrection remainder width)
        (underCorrection modulus width) (correctionExtendedCell ctx width)
        (writeUnderCorrection output width) before.1
      ((result.1, before.2), result.2)) ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (correctionBody_execute (model := model) (underCorrection remainder width)
      (underCorrection modulus width) (correctionExtendedCell ctx width)
      (writeUnderCorrection output width) reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

private theorem correctionExtended_free {shape : CShape} (input : CInputRef ctx shape) :
    (correctionExtendedCell ctx width).key ∉ (underCorrection input width).storageKeys := by
  rw [underCorrection, CInputRef.storageKeys_underWorkspace]
  exact fun present => ctx.canonicalFreshKey_fresh (input.storageKeys_subset_context present)

/-- The actual original result has its exact finite native value for every caller store. -/
theorem withNegativeCorrection_value {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (withNegativeCorrectionStep (model := model) remainder modulus output store).1.read
      (reductionRead output) =
      negativeCorrectionValue (store.read remainder) (store.read modulus) := by
  unfold withNegativeCorrectionStep
  rw [Store.read_popWorkspace_underWorkspace _ _ _ _ (reductionRead output)]
  change (correctionBodyStep (model := model) _ _ _ _ _).1.read
    (reductionRead (writeUnderCorrection output width)) = _
  rw [correctionBody_value _ _ _ _ _ (correctionExtended_free modulus)]
  simp only [underCorrection, Store.read_pushWorkspace_underWorkspace]

/-- Only the caller result key may change once both actual scratch scopes have been released. -/
theorem withNegativeCorrection_read_other {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (withNegativeCorrectionStep (model := model) remainder modulus output store).1.read other =
      store.read other := by
  unfold withNegativeCorrectionStep
  rw [Store.read_popWorkspace_underWorkspace _ _ _ _ other]
  change (correctionBodyStep (model := model) _ _ _ _ _).1.read (underCorrection other width) = _
  rw [correctionBody_read_other _ _ _ _ _ (correctionExtended_free other)]
  · exact Store.read_pushWorkspace_underWorkspace _ _ _ _ other
  · change output.key ∉ (underCorrection other width).storageKeys
    simpa only [underCorrection, CInputRef.storageKeys_underWorkspace] using separate

/-- The original fitted modulus and canonical remainder give ordinary modular negation. -/
theorem negativeCorrectionValue_original_toNat (remainder : CShape.Word width)
    (modulus : CShape.Word (width + 1)) (spec : ModulusSpec width)
    (modulusValue : modulus.toNat = spec.modulus)
    (remainderRange : remainder.toNat < spec.modulus) :
    (negativeCorrectionValue remainder modulus).toNat =
      (spec.modulus - remainder.toNat) % spec.modulus := by
  have resizedValue : (CShape.wordResize (width + 1) remainder).toNat = remainder.toNat := by
    change remainder.toNat % 2 ^ (width + 1) = remainder.toNat
    apply Nat.mod_eq_of_lt
    exact lt_of_lt_of_le remainder.toNat_lt
      (Nat.pow_le_pow_right (by decide) (Nat.le_succ width))
  have difference : (CShape.wordSub (width + 1) modulus
      (CShape.wordResize (width + 1) remainder)).toNat = modulus.toNat - remainder.toNat := by
    have bounded : (CShape.wordResize (width + 1) remainder).toNat ≤ modulus.toNat := by
      rw [resizedValue, modulusValue]
      exact Nat.le_of_lt remainderRange
    exact (widenedWordSub_exact_of_le modulus _ bounded).trans
      (congrArg (modulus.toNat - ·) resizedValue)
  unfold negativeCorrectionValue
  rw [reductionValue_toNat _ _ (modulusValue ▸ modulusSpec_modulus_pos spec)
    (modulusValue ▸ spec.le_capacity), difference, modulusValue]

/-- Real reduction maps modulus minus zero back to zero even at full word capacity. -/
theorem withNegativeCorrection_original_value {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (remainder : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (spec : ModulusSpec width) (store : Store ctx)
    (modulusValue : (store.read modulus).toNat = spec.modulus)
    (remainderRange : (store.read remainder).toNat < spec.modulus) :
    ((withNegativeCorrectionStep (model := model) remainder modulus output store).1.read
      (reductionRead output)).toNat =
      if (store.read remainder).toNat = 0 then 0
        else spec.modulus - (store.read remainder).toNat := by
  rw [withNegativeCorrection_value,
    negativeCorrectionValue_original_toNat _ _ spec modulusValue remainderRange]
  exact correctionRemainder_eq_normalized spec _ remainderRange

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native
