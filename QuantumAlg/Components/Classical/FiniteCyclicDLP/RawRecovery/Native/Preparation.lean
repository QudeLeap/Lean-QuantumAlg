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

/-!+# Actual original raw-recovery preparation

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
def preparationDecode (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) : Circuit ctx ctx :=
  .seq (measuredDecodeInto input refs.decoded) (Word.Split.splitInto refs.split)

/-- The real decoder record feeds the real destructive split record. -/
def preparationDecodeStep (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) :
    Store ctx → Store ctx × (preparationDecode input refs).Path :=
  Circuit.sequenceRecord (measuredDecodeInto input refs.decoded) (Word.Split.splitInto refs.split)
    (measuredDecodeStep input refs.decoded) (Word.Split.splitStep refs.split)

/-- Load the original modulus, then seed the shared denominator exactly once. -/
def preparationConstants (spec : ModulusSpec width) (refs : PreparationRefs ctx width) :
    Circuit ctx ctx :=
  .seq (ConstantWord.circuit refs.modulusWide spec.modulus) (scaleSeed refs.denominator)

/-- Both original constant preparations share the actual intermediate store. -/
def preparationConstantsStep (spec : ModulusSpec width) (refs : PreparationRefs ctx width) :
    Store ctx → Store ctx × (preparationConstants spec refs).Path :=
  Circuit.sequenceRecord (ConstantWord.circuit refs.modulusWide spec.modulus)
    (scaleSeed refs.denominator)
    (ConstantWord.foldStep refs.modulusWide
      (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)))
    (scaleSeedStep refs.denominator)

/-- Normalize both original raw frequencies with their shared actual arithmetic scratch. -/
def preparationScale (refs : PreparationRefs ctx width) : Circuit ctx ctx :=
  scalePairBody (scaleRead refs.rawLeft) (scaleRead refs.rawRight)
    (scaleRead refs.modulusWide) (scaleRead refs.denominator)
    refs.product refs.division refs.left refs.right

/-- Real two-scaling store and the two chronological three-instruction paths. -/
def preparationScaleStep (refs : PreparationRefs ctx width) (store : Store ctx) :
    Store ctx × (preparationScale refs).Path :=
  (scalePairStore (scaleRead refs.rawLeft) (scaleRead refs.rawRight)
    (scaleRead refs.modulusWide) (scaleRead refs.denominator)
    refs.product refs.division refs.left refs.right store, (((), ((), ())), ((), ((), ()))))

/-- Narrow the modulus, then execute the original zero-test and selected negation instruction. -/
def preparationFinalize (refs : PreparationRefs ctx width) : Circuit ctx ctx :=
  .seq (.classical refs.narrowOp)
    (negateBody (scaleRead refs.modulus) (scaleRead refs.right) (scaleRead refs.zero)
      refs.negationFlag refs.negatedRight)

/-- The final record selects its branch from the actual comparison written to storage. -/
def preparationFinalizeStep (refs : PreparationRefs ctx width) :
    Store ctx → Store ctx × (preparationFinalize refs).Path :=
  Circuit.sequenceRecord (.classical refs.narrowOp)
    (negateBody (scaleRead refs.modulus) (scaleRead refs.right) (scaleRead refs.zero)
      refs.negationFlag refs.negatedRight)
    (fun store => (store.applyOp refs.narrowOp, ()))
    (negateBodyStep (scaleRead refs.modulus) (scaleRead refs.right) (scaleRead refs.zero)
      refs.negationFlag refs.negatedRight)

/-- The complete original decode-and-seed prefix runs before either scaling call. -/
def preparationDecodeSeed (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) : Circuit ctx ctx :=
  .seq (preparationDecode input refs) (preparationConstants spec refs)

/-- The original pair of scalings feeds the original final normalization branch. -/
def preparationScaleFinalize (refs : PreparationRefs ctx width) : Circuit ctx ctx :=
  .seq (preparationScale refs) (preparationFinalize refs)

/-- The actual full pre-engine circuit uses no supplied inverse or mathematical output write. -/
def preparationBody (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) : Circuit ctx ctx :=
  .seq (preparationDecodeSeed spec input refs) (preparationScaleFinalize refs)

/-- Every preparation phase receives the actual returned store of the preceding phase. -/
def preparationStep (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) :
    Store ctx → Store ctx × (preparationBody spec input refs).Path :=
  Circuit.sequenceRecord (preparationDecodeSeed spec input refs) (preparationScaleFinalize refs)
    (Circuit.sequenceRecord (preparationDecode input refs) (preparationConstants spec refs)
      (preparationDecodeStep input refs) (preparationConstantsStep spec refs))
    (Circuit.sequenceRecord (preparationScale refs) (preparationFinalize refs)
      (preparationScaleStep refs) (preparationFinalizeStep refs))

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
