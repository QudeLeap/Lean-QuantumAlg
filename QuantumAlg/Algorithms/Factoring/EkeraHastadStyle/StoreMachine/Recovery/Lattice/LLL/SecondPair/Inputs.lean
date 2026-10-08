/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.Classification

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.ProductDifference

/-!
# Actual second-reduction inputs

Two shared three-operation product differences compute the original Gram
expressions. The first product reuses its output cell; both expressions share
one product word. All input and output values belong to the actual store.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondReductionInputs

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The five raw Gram words consumed by the second-reduction arithmetic. -/
structure Inputs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Input reference for the g 11 value. -/
  g11 : CInputRef ctx (.unsignedWord width)
  /-- Input reference for the g 21 value. -/
  g21 : CInputRef ctx (.unsignedWord width)
  /-- Input reference for the g 31 value. -/
  g31 : CInputRef ctx (.unsignedWord width)
  /-- Input reference for the g 22 value. -/
  g22 : CInputRef ctx (.unsignedWord width)
  /-- Input reference for the g 32 value. -/
  g32 : CInputRef ctx (.unsignedWord width)

/-- Caller-owned outputs and one shared low-product scratch word. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Writable cell for the nu 32 value. -/
  nu32 : CWriteRef ctx (.unsignedWord width)
  nu32Role : nu32.toCStorageRef.role = .workspace
  /-- Writable cell for the d 32 value. -/
  d32 : CWriteRef ctx (.unsignedWord width)
  d32Role : d32.toCStorageRef.role = .workspace
  /-- Writable cell for the product value. -/
  product : CWriteRef ctx (.unsignedWord width)
  productRole : product.toCStorageRef.role = .workspace

/-- Named input words used to state source-to-write separation. -/
inductive InputCell where
  | g11
  | g21
  | g31
  | g22
  | g32
deriving DecidableEq

/-- Structural read of one named raw Gram input. -/
abbrev inputRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (inputs : Inputs ctx width) : InputCell → CInputRef ctx (.unsignedWord width)
  | .g11 => inputs.g11
  | .g21 => inputs.g21
  | .g31 => inputs.g31
  | .g22 => inputs.g22
  | .g32 => inputs.g32

/-- Named mutable words used by the six raw arithmetic instructions. -/
inductive MutableCell where
  | nu32
  | d32
  | product
deriving DecidableEq

/-- Resolve a mutable name to its caller-owned writable word. -/
abbrev mutableRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : MutableCell → CWriteRef ctx (.unsignedWord width)
  | .nu32 => refs.nu32
  | .d32 => refs.d32
  | .product => refs.product

/-- Storage identity of one mutable second-reduction word. -/
def mutableKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : MutableCell → StorageKey :=
  fun cell => (mutableRef refs cell).toCStorageRef.key

/-- Sources avoid all writes, and the three mutable words are distinct. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (inputs : Inputs ctx width) (refs : Refs ctx width) : Prop where
  inputAvoidsMutable : ∀ source cell,
    mutableKey refs cell ∉ (inputRef inputs source).storageKeys
  mutableInjective : Function.Injective (mutableKey refs)

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Distinct mutable names have distinct actual writable identities. -/
theorem Separation.mutable_ne {inputs : Inputs ctx width} {refs : Refs ctx width}
    (separation : Separation inputs refs) (left right : MutableCell) (different : left ≠ right) :
    mutableKey refs left ≠ mutableKey refs right :=
  fun equal => different (separation.mutableInjective equal)

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Reuse the output for the first product in the shared actual arithmetic component. -/
def productDifferenceInto (a b c d : CInputRef ctx (.unsignedWord width))
    (output product : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  ProductDifference.computeInto (model := model) a b c d output output product

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Actual chronological writes with the first product resident in the output word. -/
def productDifferenceStore (a b c d : CInputRef ctx (.unsignedWord width))
    (output product : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  ProductDifference.computedStore a b c d output output product store

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The two original Gram expressions, each using exactly three native operations. -/
def secondReductionInputsInto (inputs : Inputs ctx width) (refs : Refs ctx width) :
    Circuit model ctx ctx :=
  .seq (productDifferenceInto (model := model) inputs.g11 inputs.g32 inputs.g31 inputs.g21
      refs.nu32 refs.product)
    (productDifferenceInto (model := model) inputs.g11 inputs.g22 inputs.g21 inputs.g21 refs.d32
      refs.product)

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Actual numerator writes followed by actual denominator writes. -/
def secondReductionInputsStore (inputs : Inputs ctx width) (refs : Refs ctx width)
    (store : Store ctx) : Store ctx :=
  productDifferenceStore inputs.g11 inputs.g22 inputs.g21 inputs.g21 refs.d32 refs.product
    (productDifferenceStore inputs.g11 inputs.g32 inputs.g31 inputs.g21
      refs.nu32 refs.product store)

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The two actual three-operation records on their chronological stores. -/
def secondReductionInputsStep (inputs : Inputs ctx width) (refs : Refs ctx width)
    (store : Store ctx) :
    Store ctx × (secondReductionInputsInto (model := model) inputs refs).Path :=
  let first := ProductDifference.computationStep (model := model)
    inputs.g11 inputs.g32 inputs.g31 inputs.g21 refs.nu32 refs.nu32 refs.product store
  let second := ProductDifference.computationStep (model := model)
    inputs.g11 inputs.g22 inputs.g21 inputs.g21 refs.d32 refs.d32 refs.product first.1
  (second.1, (first.2, second.2))

/-- Complete actual execution preserves history and full quantum-reference correlations. -/
theorem secondReductionInputsInto_execute (inputs : Inputs ctx width) (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (secondReductionInputsInto (model := model) inputs refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := secondReductionInputsStep (model := model) inputs refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  unfold secondReductionInputsInto productDifferenceInto secondReductionInputsStep
  refine (Circuit.execute_seq_mapClassical _ _
    (fun before =>
      let actual := ProductDifference.computationStep (model := model)
        inputs.g11 inputs.g32 inputs.g31 inputs.g21 refs.nu32 refs.nu32 refs.product before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := ProductDifference.computationStep (model := model)
        inputs.g11 inputs.g22 inputs.g21 inputs.g21 refs.d32 refs.d32 refs.product before.1
      ((actual.1, before.2), actual.2)) ?_ ?_ Reference state).trans ?_
  · intro reference history _ current
    exact ProductDifference.computeInto_execute _ _ _ _ _ _ _ reference current
  · intro reference history _ current
    exact ProductDifference.computeInto_execute _ _ _ _ _ _ _ reference current
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Reads outside the two actual product-difference writes are preserved exactly. -/
theorem productDifference_callerFrame (a b c d : CInputRef ctx (.unsignedWord width))
    (output product : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoidsOutput : output.key ∉ other.storageKeys)
    (avoidsProduct : product.key ∉ other.storageKeys) :
    (productDifferenceStore a b c d output product store).read other = store.read other :=
  ProductDifference.computeInto_callerFrame a b c d output output product store other
    avoidsOutput avoidsOutput avoidsProduct

/-- All actual caller reads outside the two output words and shared scratch survive both stages. -/
theorem secondReductionInputsInto_callerFrame (inputs : Inputs ctx width) (refs : Refs ctx width)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (numerator : refs.nu32.key ∉ other.storageKeys) (denominator : refs.d32.key ∉ other.storageKeys)
    (product : refs.product.key ∉ other.storageKeys) :
    (secondReductionInputsStore inputs refs store).read other = store.read other := by
  unfold secondReductionInputsStore
  rw [productDifference_callerFrame _ _ _ _ _ _ _ other denominator product,
    productDifference_callerFrame _ _ _ _ _ _ _ other numerator product]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondReductionInputs
