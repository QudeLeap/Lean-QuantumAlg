/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Decode
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Scale.Pair
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Scale.Placement
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Negate.Semantics
import all QuantumAlg.Components.Classical.Word.Split.Correctness
import all QuantumAlg.Components.Classical.ConstantWord.Semantics
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Actual original raw-recovery preparation

Actual measured bits are decoded and split before the original modulus loader
and the single denominator seed. Both frequency scalings reuse the same full
product and division cells. Modulus narrowing then precedes the original
zero-test and modular-negation branch. These are the original pre-engine
instructions; lexical initialization is supplied by the enclosing allocator.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original thirteen live preparation cells retain their actual storage identities. -/
structure PreparationRefs (ctx : RuntimeCtx kind) (width : Nat) where
  decoded : CWriteRef ctx (.unsignedWord (width + width))
  rawLeft : CWriteRef ctx (.unsignedWord width)
  rawRight : CWriteRef ctx (.unsignedWord width)
  modulusWide : CWriteRef ctx (.unsignedWord (width + 1))
  denominator : CWriteRef ctx (.unsignedWord (width + 1))
  product : CWriteRef ctx (.unsignedWord (width + (width + 1)))
  division : CWriteRef ctx (scaleDivisionShape width)
  left : CWriteRef ctx (.unsignedWord width)
  right : CWriteRef ctx (.unsignedWord width)
  modulus : CWriteRef ctx (.unsignedWord width)
  zero : CWriteRef ctx (.unsignedWord width)
  negatedRight : CWriteRef ctx (.unsignedWord width)
  negationFlag : CWriteRef ctx .bit

/-- The destructive splitter uses precisely the original decoded and raw-result words. -/
def PreparationRefs.split (refs : PreparationRefs ctx width) : Word.Split.Refs ctx width width :=
  ⟨refs.decoded, refs.rawLeft, refs.rawRight⟩

/-- The original loaded modulus is narrowed by one actual native instruction. -/
def PreparationRefs.narrowOp (refs : PreparationRefs ctx width) :
    ClassicalOp (.unsignedWord (width + 1)) (.unsignedWord width) ctx ctx :=
  .wordResize (width + 1) width ctx (scaleRead refs.modulusWide) refs.modulus

/-- Decode the actual measured values and split the resulting combined-width word. -/
def preparationDecode {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) : Circuit model ctx ctx :=
  .seq (measuredDecodeInto (model := model) input refs.decoded)
    (Word.Split.splitInto (model := model) refs.split)

/-- The real decoder record feeds the real destructive split record. -/
def preparationDecodeStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) :
    Store ctx → Store ctx × (preparationDecode (model := model) input refs).Path :=
  fun store =>
    let decoded := measuredDecodeStep (model := model) input refs.decoded store
    let split := Word.Split.splitStep (model := model) refs.split decoded.1
    (split.1, (decoded.2, split.2))

/-- Load the original modulus, then seed the shared denominator exactly once. -/
def preparationConstants {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : ModulusSpec width) (refs : PreparationRefs ctx width) :
    Circuit model ctx ctx :=
  .seq (ConstantWord.circuit (model := model) refs.modulusWide spec.modulus)
    (scaleSeed (model := model) refs.denominator)

/-- Both original constant preparations share the actual intermediate store. -/
def preparationConstantsStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : ModulusSpec width) (refs : PreparationRefs ctx width) :
    Store ctx → Store ctx × (preparationConstants (model := model) spec refs).Path :=
  fun store =>
    let loaded := ConstantWord.foldStep (model := model) refs.modulusWide
      (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) store
    let seeded := scaleSeedStep (model := model) refs.denominator loaded.1
    (seeded.1, (loaded.2, seeded.2))

/-- Normalize both original raw frequencies with their shared actual arithmetic scratch. -/
def preparationScale {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : PreparationRefs ctx width) : Circuit model ctx ctx :=
  scalePairBody (model := model) (scaleRead refs.rawLeft) (scaleRead refs.rawRight)
    (scaleRead refs.modulusWide) (scaleRead refs.denominator)
    refs.product refs.division refs.left refs.right

/-- Real two-scaling store and the two chronological three-instruction paths. -/
def preparationScaleStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : PreparationRefs ctx width) (store : Store ctx) :
    Store ctx × (preparationScale (model := model) refs).Path :=
  scalePairStep (model := model) (scaleRead refs.rawLeft) (scaleRead refs.rawRight)
    (scaleRead refs.modulusWide) (scaleRead refs.denominator)
    refs.product refs.division refs.left refs.right store

/-- Narrow the modulus, then execute the original zero-test and selected negation instruction. -/
def preparationFinalize {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : PreparationRefs ctx width) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) refs.narrowOp)
    (negateBody (model := model) (scaleRead refs.modulus) (scaleRead refs.right)
      (scaleRead refs.zero)
      refs.negationFlag refs.negatedRight)

/-- The final record selects its branch from the actual comparison written to storage. -/
def preparationFinalizeStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : PreparationRefs ctx width) :
    Store ctx → Store ctx × (preparationFinalize (model := model) refs).Path :=
  fun store =>
    let narrowed := BitWord.instructionStep (execution := model) refs.narrowOp store
    let negated := negateBodyStep (model := model) (scaleRead refs.modulus) (scaleRead refs.right)
      (scaleRead refs.zero) refs.negationFlag refs.negatedRight narrowed.1
    (negated.1, (narrowed.2, negated.2))

/-- The complete original decode-and-seed prefix runs before either scaling call. -/
def preparationDecodeSeed {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) : Circuit model ctx ctx :=
  .seq (preparationDecode (model := model) input refs)
    (preparationConstants (model := model) spec refs)

/-- The original pair of scalings feeds the original final normalization branch. -/
def preparationScaleFinalize {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : PreparationRefs ctx width) : Circuit model ctx ctx :=
  .seq (preparationScale (model := model) refs) (preparationFinalize (model := model) refs)

/-- The actual full pre-engine circuit uses no supplied inverse or mathematical output write. -/
def preparationBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) : Circuit model ctx ctx :=
  .seq (preparationDecodeSeed (model := model) spec input refs)
    (preparationScaleFinalize (model := model) refs)

/-- Every preparation phase receives the actual returned store of the preceding phase. -/
def preparationStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) :
    Store ctx → Store ctx × (preparationBody (model := model) spec input refs).Path :=
  fun store =>
    let decoded := preparationDecodeStep (model := model) input refs store
    let seeded := preparationConstantsStep (model := model) spec refs decoded.1
    let scaled := preparationScaleStep (model := model) refs seeded.1
    let finalized := preparationFinalizeStep (model := model) refs scaled.1
    (finalized.1, ((decoded.2, seeded.2), (scaled.2, finalized.2)))

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
