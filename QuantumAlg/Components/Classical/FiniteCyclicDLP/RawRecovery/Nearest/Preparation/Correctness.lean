/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Execution
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Model
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Correctness

/-!
# Exact normalized values from actual nearest preparation

Fresh separation protects the public modulus, complete raw values and the
power-of-two denominator throughout both paid nearest scalings.  The original
actual sign branch then supplies the canonical negative right residue.  No
incoming scratch values are assumed beyond the two actual lexical initializers.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest

open Execution ClassicalAlgorithms.Modular RawRecovery.Native

noncomputable section

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Fourteen actual preparation cells keep their original identities pairwise separate. -/
structure PreparationSeparation (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1)))) : Prop where
  native : refs.Separated
  halfDifferent : ∀ index : Fin 13, half.key ≠ refs.key index

private lemma key_free (refs : PreparationRefs ctx width) (separate : refs.Separated)
    (left right : Fin 13) (different : left ≠ right) : refs.key left ∉ [refs.key right] :=
  fun member => refs.key_ne separate left right different (List.mem_singleton.mp member)

private lemma half_free (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (separate : PreparationSeparation refs half) (index : Fin 13) :
    half.key ∉ [refs.key index] :=
  fun member => separate.halfDifferent index (List.mem_singleton.mp member)

lemma PreparationSeparation.scale (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (separate : PreparationSeparation refs half) (right : Bool) :
    ScaleSeparation (scaleRefs refs half right) :=
  ⟨key_free refs separate.native 5 3 (by decide),
    key_free refs separate.native 5 4 (by decide),
    half_free refs half separate 3, half_free refs half separate 4,
    half_free refs half separate 5, key_free refs separate.native 6 3 (by decide)⟩

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Both actual nearest scalings preserve every structural read outside their five cells. -/
lemma preparationScale_read_other (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    {shape : CShape} (other : CInputRef ctx shape)
    (productFree : refs.product.key ∉ other.storageKeys)
    (divisionFree : refs.division.key ∉ other.storageKeys)
    (leftFree : refs.left.key ∉ other.storageKeys)
    (rightFree : refs.right.key ∉ other.storageKeys)
    (halfFree : half.key ∉ other.storageKeys) (store : Store ctx) :
    (preparationScaleStep (model := model) refs half store).1.read other = store.read other :=
  (scaleStep_read_other (model := model) (scaleRefs refs half true) other productFree halfFree
    divisionFree rightFree _).trans
    (scaleStep_read_other (model := model) (scaleRefs refs half false) other productFree halfFree
      divisionFree leftFree store)

/-- Both actual nearest scalings compute their exact canonical mathematical residues. -/
lemma preparationScale_nearest_values (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (separate : PreparationSeparation refs half) (store : Store ctx)
    (modulusValue : (store.read (scaleRead refs.modulusWide)).toNat = spec.modulus)
    (denominatorValue : (store.read (scaleRead refs.denominator)).toNat = 2 ^ width) :
    ((preparationScaleStep (model := model) refs half store).1.read
      (scaleRead refs.left)).toNat =
        NearestResidue.quotient ((store.read (scaleRead refs.rawLeft)).toNat * spec.modulus)
          (2 ^ width) % spec.modulus ∧
      ((preparationScaleStep (model := model) refs half store).1.read
        (scaleRead refs.right)).toNat =
        NearestResidue.quotient ((store.read (scaleRead refs.rawRight)).toNat * spec.modulus)
          (2 ^ width) % spec.modulus := by
  let first := (scaleStep (model := model) (scaleRefs refs half false) store).1
  have firstRead (index : Fin 13) (productFree : refs.key 5 ≠ refs.key index)
      (divisionFree : refs.key 6 ≠ refs.key index) (outputFree : refs.key 7 ≠ refs.key index)
      {shape : CShape} (other : CInputRef ctx shape)
      (support : other.storageKeys = [refs.key index]) : first.read other = store.read other :=
    scaleStep_read_other (model := model) (scaleRefs refs half false) other
      (by rw [support]; exact fun member => productFree (List.mem_singleton.mp member))
      (by rw [support]; exact half_free refs half separate index)
      (by rw [support]; exact fun member => divisionFree (List.mem_singleton.mp member))
      (by rw [support]; exact fun member => outputFree (List.mem_singleton.mp member)) store
  have orderRead := firstRead 3 (refs.key_ne separate.native 5 3 (by decide))
    (refs.key_ne separate.native 6 3 (by decide))
    (refs.key_ne separate.native 7 3 (by decide)) (scaleRead refs.modulusWide) rfl
  have denominatorRead := firstRead 4 (refs.key_ne separate.native 5 4 (by decide))
    (refs.key_ne separate.native 6 4 (by decide))
    (refs.key_ne separate.native 7 4 (by decide)) (scaleRead refs.denominator) rfl
  have rightRead := firstRead 2 (refs.key_ne separate.native 5 2 (by decide))
    (refs.key_ne separate.native 6 2 (by decide))
    (refs.key_ne separate.native 7 2 (by decide)) (scaleRead refs.rawRight) rfl
  have leftValue := scaleStep_nearest (model := model) (scaleRefs refs half false)
    (PreparationSeparation.scale refs half separate false) store spec modulusValue denominatorValue
  have rightValue := scaleStep_nearest (model := model) (scaleRefs refs half true)
    (PreparationSeparation.scale refs half separate true) first spec
    ((congrArg CShape.Value.toNat orderRead).trans modulusValue)
    ((congrArg CShape.Value.toNat denominatorRead).trans denominatorValue)
  have leftRead := scaleStep_read_other (model := model) (scaleRefs refs half true)
    (scaleRead refs.left) (key_free refs separate.native 5 7 (by decide))
    (half_free refs half separate 7) (key_free refs separate.native 6 7 (by decide))
    (key_free refs separate.native 8 7 (by decide)) first
  refine ⟨(congrArg CShape.Value.toNat leftRead).trans leftValue, ?_⟩
  exact rightValue.trans (congrArg
    (fun value : CShape.Value (.unsignedWord width) =>
      NearestResidue.quotient (value.toNat * spec.modulus) (2 ^ width) % spec.modulus) rightRead)

/-- The complete actual pre-engine store contains exactly the original normalized inputs. -/
lemma preparationBody_original_values {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (separate : PreparationSeparation refs half) (store : Store ctx)
    (denominatorZero : (store.read (scaleRead refs.denominator)).toNat = 0)
    (zeroValue : (store.read (scaleRead refs.zero)).toNat = 0) :
    let original := normalize spec (leftRaw (preparationInput (store.read input)))
      (rightRaw (preparationInput (store.read input)))
    let final := (preparationStep (model := model) spec input refs half store).1
    (final.read (scaleRead refs.modulusWide)).toNat = spec.modulus ∧
      (final.read (scaleRead refs.left)).toNat = original.left.val ∧
      (final.read (scaleRead refs.negatedRight)).toNat = (negateRight spec original).val := by
  let decoded := (preparationDecodeStep (model := model) input refs store).1
  let loaded := (preparationConstantsStep (model := model) spec refs decoded).1
  let scaled := (preparationScaleStep (model := model) refs half loaded).1
  let original := normalize spec (leftRaw (preparationInput (store.read input)))
      (rightRaw (preparationInput (store.read input)))
  have raw := preparationDecode_values (model := model) input refs separate.native store
  have initialDenominator : (decoded.read (scaleRead refs.denominator)).toNat = 0 :=
    (congrArg CShape.Value.toNat (preparationDecode_read_other (model := model) input refs
      (scaleRead refs.denominator) (key_free refs separate.native 0 4 (by decide))
      (key_free refs separate.native 1 4 (by decide))
      (key_free refs separate.native 2 4 (by decide))
      store)).trans denominatorZero
  have constants := preparationConstants_values (model := model) spec refs separate.native decoded
    initialDenominator
  have leftRawRead : loaded.read (scaleRead refs.rawLeft) =
      decoded.read (scaleRead refs.rawLeft) :=
    preparationConstants_read_other (model := model) spec refs (scaleRead refs.rawLeft)
      (key_free refs separate.native 3 1 (by decide))
      (key_free refs separate.native 4 1 (by decide)) decoded
  have rightRawRead : loaded.read (scaleRead refs.rawRight) =
      decoded.read (scaleRead refs.rawRight) :=
    preparationConstants_read_other (model := model) spec refs (scaleRead refs.rawRight)
      (key_free refs separate.native 3 2 (by decide))
      (key_free refs separate.native 4 2 (by decide)) decoded
  have scaleValues := preparationScale_nearest_values (model := model) spec refs half separate
    loaded constants.1 constants.2
  have leftValue : (scaled.read (scaleRead refs.left)).toNat = original.left.val := by
    refine scaleValues.1.trans ?_
    rw [leftRawRead]
    exact congrArg (fun value =>
      NearestResidue.quotient (value * spec.modulus) (2 ^ width) % spec.modulus) raw.1
  have rightValue : (scaled.read (scaleRead refs.right)).toNat = original.right.val := by
    refine scaleValues.2.trans ?_
    rw [rightRawRead]
    exact congrArg (fun value =>
      NearestResidue.quotient (value * spec.modulus) (2 ^ width) % spec.modulus) raw.2
  have modulusRead : scaled.read (scaleRead refs.modulusWide) =
      loaded.read (scaleRead refs.modulusWide) :=
    preparationScale_read_other (model := model) refs half (scaleRead refs.modulusWide)
      (key_free refs separate.native 5 3 (by decide))
      (key_free refs separate.native 6 3 (by decide))
      (key_free refs separate.native 7 3 (by decide))
      (key_free refs separate.native 8 3 (by decide))
      (half_free refs half separate 3) loaded
  have modulusValue : (scaled.read (scaleRead refs.modulusWide)).toNat = spec.modulus :=
    (congrArg CShape.Value.toNat modulusRead).trans constants.1
  have zeroRead : scaled.read (scaleRead refs.zero) = store.read (scaleRead refs.zero) :=
    (preparationScale_read_other (model := model) refs half (scaleRead refs.zero)
      (key_free refs separate.native 5 10 (by decide))
      (key_free refs separate.native 6 10 (by decide))
      (key_free refs separate.native 7 10 (by decide))
      (key_free refs separate.native 8 10 (by decide))
      (half_free refs half separate 10) loaded).trans
      ((preparationConstants_read_other (model := model) spec refs (scaleRead refs.zero)
        (key_free refs separate.native 3 10 (by decide))
        (key_free refs separate.native 4 10 (by decide)) decoded).trans
        (preparationDecode_read_other (model := model) input refs (scaleRead refs.zero)
          (key_free refs separate.native 0 10 (by decide))
          (key_free refs separate.native 1 10 (by decide))
          (key_free refs separate.native 2 10 (by decide)) store))
  have finalModulus := preparationFinalize_read_other (model := model) refs (scaleRead
    refs.modulusWide)
    (key_free refs separate.native 9 3 (by decide)) (key_free refs separate.native 12 3 (by decide))
    (key_free refs separate.native 11 3 (by decide)) scaled
  have finalLeft := preparationFinalize_read_other (model := model) refs (scaleRead refs.left)
    (key_free refs separate.native 9 7 (by decide)) (key_free refs separate.native 12 7 (by decide))
    (key_free refs separate.native 11 7 (by decide)) scaled
  have finalNegative := preparationFinalize_original_value (model := model) spec refs
    separate.native scaled modulusValue
    (by rw [rightValue]; exact original.right.isLt)
    ((congrArg CShape.Value.toNat zeroRead).trans zeroValue)
  exact ⟨(congrArg CShape.Value.toNat finalModulus).trans modulusValue,
    (congrArg CShape.Value.toNat finalLeft).trans leftValue,
    finalNegative.trans (by rw [rightValue]; rfl)⟩


/-- The complete nearest prefix preserves every caller read outside its fourteen actual cells. -/
lemma preparationBody_read_other (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    {shape : CShape} (other : CInputRef ctx shape)
    (free : ∀ index : Fin 13, refs.key index ∉ other.storageKeys)
    (halfFree : half.key ∉ other.storageKeys) (store : Store ctx) :
    (preparationStep (model := model) spec input refs half store).1.read other = store.read other :=
  (preparationFinalize_read_other (model := model) refs other (free 9) (free 12) (free 11) _).trans
    ((preparationScale_read_other (model := model) refs half other
      (free 5) (free 6) (free 7) (free 8) halfFree _).trans
      ((preparationConstants_read_other (model := model) spec refs other (free 3) (free 4) _).trans
        (preparationDecode_read_other (model := model) input refs other (free 0) (free 1)
          (free 2) store)))

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest
