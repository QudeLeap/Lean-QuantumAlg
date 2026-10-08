/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Values
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Original normalization from the actual complete preparation

The original modulus range includes equality with word capacity. The actual
narrowed modulus therefore retains its wrapping value. The real zero-test
branch still produces the original canonical negative frequency. Actual
lexical initialization supplies the two internal zero premises below.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem key_free (refs : PreparationRefs ctx width) (separate : refs.Separated)
    (left right : Fin 13) (different : left ≠ right) : refs.key left ∉ [refs.key right] :=
  fun member => refs.key_ne separate left right different (List.mem_singleton.mp member)

/-- The two actual scalings preserve reads outside their four reused destinations. -/
theorem preparationScale_read_other {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : PreparationRefs ctx width)
    {shape : CShape} (other : CInputRef ctx shape)
    (productFree : refs.product.key ∉ other.storageKeys)
    (divisionFree : refs.division.key ∉ other.storageKeys)
    (leftFree : refs.left.key ∉ other.storageKeys)
    (rightFree : refs.right.key ∉ other.storageKeys) (store : Store ctx) :
    (preparationScaleStep (model := model) refs store).1.read other = store.read other :=
  scalePairBody_read_other (scaleRead refs.rawLeft) (scaleRead refs.rawRight)
    (scaleRead refs.modulusWide) (scaleRead refs.denominator) refs.product refs.division
    refs.left refs.right other productFree divisionFree leftFree rightFree store

/-- Final normalization writes only the narrowed modulus, equality flag and negative frequency. -/
theorem preparationFinalize_read_other {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : PreparationRefs ctx width)
    {shape : CShape} (other : CInputRef ctx shape)
    (modulusFree : refs.modulus.key ∉ other.storageKeys)
    (flagFree : refs.negationFlag.key ∉ other.storageKeys)
    (outputFree : refs.negatedRight.key ∉ other.storageKeys) (store : Store ctx) :
    (preparationFinalizeStep (model := model) refs store).1.read other = store.read other :=
  (negateBody_read_other (model := model) (scaleRead refs.modulus) (scaleRead refs.right)
    (scaleRead refs.zero)
    refs.negationFlag refs.negatedRight _ other flagFree outputFree).trans
    (Store.read_applyOp_of_not_mem_storageKeys store refs.narrowOp other modulusFree)

/-- Actual narrowing and the original branch compute the canonical modular negative frequency. -/
theorem preparationFinalize_original_value {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width) (separate : refs.Separated) (store : Store ctx)
    (modulusValue : (store.read (scaleRead refs.modulusWide)).toNat = spec.modulus)
    (rightCanonical : (store.read (scaleRead refs.right)).toNat < spec.modulus)
    (zeroValue : (store.read (scaleRead refs.zero)).toNat = 0) :
    ((preparationFinalizeStep (model := model) refs store).1.read (scaleRead
      refs.negatedRight)).toNat =
      (spec.modulus - (store.read (scaleRead refs.right)).toNat) % spec.modulus := by
  let narrowed := store.applyOp refs.narrowOp
  have rightRead : narrowed.read (scaleRead refs.right) = store.read (scaleRead refs.right) :=
    Store.read_applyOp_of_not_mem_storageKeys store refs.narrowOp (scaleRead refs.right)
      (key_free refs separate 9 8 (by decide))
  have zeroRead : narrowed.read (scaleRead refs.zero) = store.read (scaleRead refs.zero) :=
    Store.read_applyOp_of_not_mem_storageKeys store refs.narrowOp (scaleRead refs.zero)
      (key_free refs separate 9 10 (by decide))
  have modulusRead : (narrowed.read (scaleRead refs.modulus)).toNat =
      spec.modulus % 2 ^ width := by
    have written := Store.read_applyOp_output store refs.narrowOp
    change narrowed.read (scaleRead refs.modulus) =
      CShape.wordResize width (store.read (scaleRead refs.modulusWide)) at written
    rw [written]
    change (store.read (scaleRead refs.modulusWide)).toNat % 2 ^ width = _
    rw [modulusValue]
  have actual := negateBody_result (model := model) (scaleRead refs.modulus) (scaleRead refs.right)
    (scaleRead refs.zero) refs.negationFlag refs.negatedRight
    (key_free refs separate 12 9 (by decide)) (key_free refs separate 12 8 (by decide))
    (key_free refs separate 12 10 (by decide)) narrowed
  have natural : ((preparationFinalizeStep (model := model) refs store).1.read
      (scaleRead refs.negatedRight)).toNat =
        negateNatural width (spec.modulus % 2 ^ width)
          (store.read (scaleRead refs.right)).toNat := by
    change ((negateBodyStep (model := model) (scaleRead refs.modulus) (scaleRead refs.right)
      (scaleRead refs.zero) refs.negationFlag refs.negatedRight narrowed).1.read
        (negateRead refs.negatedRight)).toNat = _
    simpa only [apply_ite CShape.Value.toNat, CShape.wordSub, CShape.wordOfNat_val,
      CShape.wordModulus, rightRead, zeroRead, zeroValue, modulusRead, negateNatural] using
      congrArg CShape.Value.toNat actual
  exact natural.trans (negateNatural_original spec _ _ rfl rightCanonical)

/-- The complete actual pre-engine store contains exactly the original normalized inputs. -/
theorem preparationBody_original_values {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (separate : refs.Separated) (store : Store ctx)
    (denominatorZero : (store.read (scaleRead refs.denominator)).toNat = 0)
    (zeroValue : (store.read (scaleRead refs.zero)).toNat = 0) :
    let original := normalize spec (preparationInput (store.read input))
    let final := (preparationStep (model := model) spec input refs store).1
    (final.read (scaleRead refs.modulusWide)).toNat = spec.modulus ∧
      (final.read (scaleRead refs.left)).toNat = original.left.val ∧
      (final.read (scaleRead refs.negatedRight)).toNat = (negateRight spec original).val := by
  let decoded := (preparationDecodeStep (model := model) input refs store).1
  let loaded := (preparationConstantsStep (model := model) spec refs decoded).1
  let scaled := (preparationScaleStep (model := model) refs loaded).1
  let original := normalize spec (preparationInput (store.read input))
  have raw := preparationDecode_values (model := model) input refs separate store
  have initialDenominator : (decoded.read (scaleRead refs.denominator)).toNat = 0 :=
    (congrArg CShape.Value.toNat (preparationDecode_read_other (model := model) input refs
      (scaleRead refs.denominator) (key_free refs separate 0 4 (by decide))
      (key_free refs separate 1 4 (by decide)) (key_free refs separate 2 4 (by decide))
      store)).trans denominatorZero
  have constants := preparationConstants_values (model := model) spec refs separate decoded
    initialDenominator
  have leftRawRead : loaded.read (scaleRead refs.rawLeft) =
      decoded.read (scaleRead refs.rawLeft) :=
    preparationConstants_read_other (model := model) spec refs (scaleRead refs.rawLeft)
      (key_free refs separate 3 1 (by decide))
      (key_free refs separate 4 1 (by decide)) decoded
  have rightRawRead : loaded.read (scaleRead refs.rawRight) =
      decoded.read (scaleRead refs.rawRight) :=
    preparationConstants_read_other (model := model) spec refs (scaleRead refs.rawRight)
      (key_free refs separate 3 2 (by decide))
      (key_free refs separate 4 2 (by decide)) decoded
  have scaleValues := preparationScale_original_values (model := model) spec refs separate loaded
    constants.1 constants.2
  have leftValue : (scaled.read (scaleRead refs.left)).toNat = original.left.val := by
    refine scaleValues.1.trans ?_
    rw [leftRawRead]
    exact congrArg (fun value => (scaleFrequency spec value).val) raw.1
  have rightValue : (scaled.read (scaleRead refs.right)).toNat = original.right.val := by
    refine scaleValues.2.trans ?_
    rw [rightRawRead]
    exact congrArg (fun value => (scaleFrequency spec value).val) raw.2
  have modulusRead : scaled.read (scaleRead refs.modulusWide) =
      loaded.read (scaleRead refs.modulusWide) :=
    preparationScale_read_other (model := model) refs (scaleRead refs.modulusWide)
      (key_free refs separate 5 3 (by decide))
      (key_free refs separate 6 3 (by decide)) (key_free refs separate 7 3 (by decide))
      (key_free refs separate 8 3 (by decide)) loaded
  have modulusValue : (scaled.read (scaleRead refs.modulusWide)).toNat = spec.modulus :=
    (congrArg CShape.Value.toNat modulusRead).trans constants.1
  have zeroRead : scaled.read (scaleRead refs.zero) = store.read (scaleRead refs.zero) :=
    (preparationScale_read_other (model := model) refs (scaleRead refs.zero)
      (key_free refs separate 5 10 (by decide))
      (key_free refs separate 6 10 (by decide)) (key_free refs separate 7 10 (by decide))
      (key_free refs separate 8 10 (by decide)) loaded).trans
      ((preparationConstants_read_other (model := model) spec refs (scaleRead refs.zero)
        (key_free refs separate 3 10 (by decide))
        (key_free refs separate 4 10 (by decide)) decoded).trans
        (preparationDecode_read_other (model := model) input refs (scaleRead refs.zero)
          (key_free refs separate 0 10 (by decide))
          (key_free refs separate 1 10 (by decide))
          (key_free refs separate 2 10 (by decide)) store))
  have finalModulus := preparationFinalize_read_other (model := model) refs (scaleRead
    refs.modulusWide)
    (key_free refs separate 9 3 (by decide)) (key_free refs separate 12 3 (by decide))
    (key_free refs separate 11 3 (by decide)) scaled
  have finalLeft := preparationFinalize_read_other (model := model) refs (scaleRead refs.left)
    (key_free refs separate 9 7 (by decide)) (key_free refs separate 12 7 (by decide))
    (key_free refs separate 11 7 (by decide)) scaled
  have finalNegative := preparationFinalize_original_value (model := model) spec refs separate
    scaled modulusValue
    (by rw [rightValue]; exact original.right.isLt)
    ((congrArg CShape.Value.toNat zeroRead).trans zeroValue)
  exact ⟨(congrArg CShape.Value.toNat finalModulus).trans modulusValue,
    (congrArg CShape.Value.toNat finalLeft).trans leftValue,
    finalNegative.trans (by rw [rightValue]; rfl)⟩

/-- The complete actual prefix preserves every structural caller read outside its live cells. -/
theorem preparationBody_read_other {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) {shape : CShape} (other : CInputRef ctx shape)
    (free : ∀ index : Fin 13, refs.key index ∉ other.storageKeys) (store : Store ctx) :
    (preparationStep (model := model) spec input refs store).1.read other = store.read other :=
  (preparationFinalize_read_other (model := model) refs other (free 9) (free 12) (free 11) _).trans
    ((preparationScale_read_other (model := model) refs other (free 5) (free 6) (free 7) (free
      8) _).trans
      ((preparationConstants_read_other (model := model) spec refs other (free 3) (free 4) _).trans
        (preparationDecode_read_other (model := model) input refs other (free 0) (free 1) (free
          2) store)))

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
