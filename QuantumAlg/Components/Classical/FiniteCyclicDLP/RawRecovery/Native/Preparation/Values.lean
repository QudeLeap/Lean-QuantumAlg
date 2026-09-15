/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation

/-!
# Original measured values through raw-recovery preparation

Storage separation below is a structural property of the original thirteen
internal cells. The enclosing real allocator supplies it. The actual decoder
and split recover the original two raw frequencies, before any normalization.
The single constant-preparation phase retains both raw words and loads the
original order and exact power-of-two denominator.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original preparation keys in their chronological allocation order. -/
def PreparationRefs.keys (refs : PreparationRefs ctx width) : List StorageKey :=
  [refs.decoded.key, refs.rawLeft.key, refs.rawRight.key, refs.modulusWide.key,
    refs.denominator.key, refs.product.key, refs.division.key, refs.left.key,
    refs.right.key, refs.modulus.key, refs.zero.key, refs.negatedRight.key,
    refs.negationFlag.key]

/-- Index one original internal key without changing its storage identity. -/
def PreparationRefs.key (refs : PreparationRefs ctx width) (index : Fin 13) : StorageKey :=
  refs.keys.get ⟨index.val, index.isLt⟩

/-- Actual internal preparation cells have different storage identities. -/
def PreparationRefs.Separated (refs : PreparationRefs ctx width) : Prop :=
  Function.Injective refs.key

/-- Different original internal positions give the precise key inequality used by execution. -/
theorem PreparationRefs.key_ne (refs : PreparationRefs ctx width) (separate : refs.Separated)
    (left right : Fin 13) (different : left ≠ right) : refs.key left ≠ refs.key right :=
  fun same => different (separate same)

/-- Fresh preparation cells supply the original split's three internal key inequalities. -/
theorem PreparationRefs.split_separation (refs : PreparationRefs ctx width)
    (separate : refs.Separated) : Word.Split.Separation refs.split :=
  ⟨refs.key_ne separate 0 2 (by decide), refs.key_ne separate 0 1 (by decide),
    refs.key_ne separate 1 2 (by decide)⟩

/-- Fresh preparation cells protect the original source reads while arithmetic scratch is reused. -/
theorem PreparationRefs.scale_separation (refs : PreparationRefs ctx width)
    (separate : refs.Separated) :
    ScalePairSeparation (scaleRead refs.rawRight) (scaleRead refs.modulusWide)
      (scaleRead refs.denominator) refs.product refs.division refs.left refs.right := by
  have free (left right : Fin 13) (different : left ≠ right) :
      refs.key left ∉ [refs.key right] :=
    fun member => refs.key_ne separate left right different (List.mem_singleton.mp member)
  exact ⟨free 5 4 (by decide), free 6 4 (by decide), free 7 4 (by decide),
    free 5 3 (by decide), free 6 3 (by decide), free 7 3 (by decide),
    free 5 2 (by decide), free 6 2 (by decide), free 7 2 (by decide),
    free 5 7 (by decide), free 6 7 (by decide), free 8 7 (by decide)⟩

/-- Pure specification of the actual finite measurement values, in original big-endian order. -/
def preparationInput (value : CShape.Value (.fixedVector (width + width) (.finite 2))) :
    CShape.Value (InputShape width) :=
  .bits (measuredDecodeInput value).bits

/-- Actual decoder and split produce the same two raw frequencies as the original input model. -/
theorem preparationDecode_values
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (separate : refs.Separated) (store : Store ctx) :
    ((preparationDecodeStep input refs store).1.read (scaleRead refs.rawLeft)).toNat =
        leftRaw (preparationInput (store.read input)) ∧
      ((preparationDecodeStep input refs store).1.read (scaleRead refs.rawRight)).toNat =
        rightRaw (preparationInput (store.read input)) := by
  let decoded := (measuredDecodeStep input refs.decoded store).1
  have value : (decoded.read (scaleRead refs.decoded)).toNat =
      decodedTerminal (preparationInput (store.read input)) :=
    measuredDecodeInto_read_output input refs.decoded store
  exact ⟨(Word.Split.splitInto_high refs.split (refs.split_separation separate) decoded).trans
      (congrArg (fun word => word / 2 ^ width) value),
    (Word.Split.splitInto_low refs.split (refs.split_separation separate) decoded).trans
      (congrArg (fun word => word % 2 ^ width) value)⟩

/-- The decode-and-split phase changes no read outside its three real destinations. -/
theorem preparationDecode_read_other
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) {shape : CShape} (other : CInputRef ctx shape)
    (decodedFree : refs.decoded.key ∉ other.storageKeys)
    (leftFree : refs.rawLeft.key ∉ other.storageKeys)
    (rightFree : refs.rawRight.key ∉ other.storageKeys) (store : Store ctx) :
    (preparationDecodeStep input refs store).1.read other = store.read other :=
  (Word.Split.splitInto_callerFrame refs.split _ other decodedFree leftFree rightFree).trans
    (measuredDecodeInto_read_other input refs.decoded store other decodedFree)

/-- Both original constants are loaded exactly; the internal denominator starts at actual zero. -/
theorem preparationConstants_values (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width) (separate : refs.Separated) (store : Store ctx)
    (initialZero : (store.read (scaleRead refs.denominator)).toNat = 0) :
    ((preparationConstantsStep spec refs store).1.read (scaleRead refs.modulusWide)).toNat =
        spec.modulus ∧
      ((preparationConstantsStep spec refs store).1.read (scaleRead refs.denominator)).toNat =
        2 ^ width := by
  let loaded := (ConstantWord.foldStep refs.modulusWide
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) store).1
  have different : refs.modulusWide.key ≠ refs.denominator.key :=
    refs.key_ne separate 3 4 (by decide)
  have modulusFree : refs.denominator.key ∉ (scaleRead refs.modulusWide).storageKeys := by
    simpa only [scaleRead, CInputRef.storageKeys, List.mem_singleton] using different.symm
  have denominatorFree : refs.modulusWide.key ∉ (scaleRead refs.denominator).storageKeys := by
    simpa only [scaleRead, CInputRef.storageKeys, List.mem_singleton] using different
  constructor
  · exact (congrArg CShape.Value.toNat
      (scaleSeed_read_other refs.denominator loaded (scaleRead refs.modulusWide)
        modulusFree)).trans
      ((ConstantWord.constantWord_read refs.modulusWide spec.modulus store).trans
        (Nat.mod_eq_of_lt (modulusSpec_modulus_lt_extended spec)))
  · apply scaleSeed_zero_value refs.denominator loaded
    exact (congrArg CShape.Value.toNat
      (ConstantWord.constantWord_fold_read_other refs.modulusWide _
        (scaleRead refs.denominator) denominatorFree store)).trans initialZero

/-- The original two loaders preserve every read outside their actual two constant cells. -/
theorem preparationConstants_read_other (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width) {shape : CShape} (other : CInputRef ctx shape)
    (modulusFree : refs.modulusWide.key ∉ other.storageKeys)
    (denominatorFree : refs.denominator.key ∉ other.storageKeys) (store : Store ctx) :
    (preparationConstantsStep spec refs store).1.read other = store.read other :=
  (scaleSeed_read_other refs.denominator _ other denominatorFree).trans
    (ConstantWord.constantWord_fold_read_other refs.modulusWide _ other modulusFree store)

/-- The exact stored original constants make both native scaling results the original residues. -/
theorem preparationScale_original_values (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width) (separate : refs.Separated) (store : Store ctx)
    (modulusValue : (store.read (scaleRead refs.modulusWide)).toNat = spec.modulus)
    (denominatorValue : (store.read (scaleRead refs.denominator)).toNat = 2 ^ width) :
    ((preparationScaleStep refs store).1.read (scaleRead refs.left)).toNat =
        (scaleFrequency spec (store.read (scaleRead refs.rawLeft)).toNat).val ∧
      ((preparationScaleStep refs store).1.read (scaleRead refs.right)).toNat =
        (scaleFrequency spec (store.read (scaleRead refs.rawRight)).toNat).val := by
  have values := scalePairBody_results (scaleRead refs.rawLeft) (scaleRead refs.rawRight)
    (scaleRead refs.modulusWide) (scaleRead refs.denominator)
    refs.product refs.division refs.left refs.right (refs.scale_separation separate) store
  exact ⟨(congrArg CShape.Value.toNat values.1).trans
      (scaleWordValue_original spec _ _ _ modulusValue denominatorValue),
    (congrArg CShape.Value.toNat values.2).trans
      (scaleWordValue_original spec _ _ _ modulusValue denominatorValue)⟩

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
