/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Scale

/-!
# Original two-frequency scaling with shared actual scratch

The two original three-instruction scaling calls reuse the same full product
and quotient/remainder cells. They read one already loaded modulus and one
already seeded denominator. This fragment does not load either constant again.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

section Descriptor

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The second scaling starts in the actual first scaling's returned store. -/
def scalePairStore (rawLeft rawRight : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (left right : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  scaleStore rawRight modulus denominator product division right
    (scaleStore rawLeft modulus denominator product division left store)

/-- Protect the later source reads and first output while the original scratch is reused. -/
structure ScalePairSeparation (rawRight : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (left right : CWriteRef ctx (.unsignedWord width)) : Prop where
  productDenominator : product.key ∉ denominator.storageKeys
  divisionDenominator : division.key ∉ denominator.storageKeys
  leftDenominator : left.key ∉ denominator.storageKeys
  productModulus : product.key ∉ modulus.storageKeys
  divisionModulus : division.key ∉ modulus.storageKeys
  leftModulus : left.key ∉ modulus.storageKeys
  productRight : product.key ∉ rawRight.storageKeys
  divisionRight : division.key ∉ rawRight.storageKeys
  leftRight : left.key ∉ rawRight.storageKeys
  productLeft : product.key ∉ (scaleRead left).storageKeys
  divisionLeft : division.key ∉ (scaleRead left).storageKeys
  rightLeft : right.key ∉ (scaleRead left).storageKeys

/-- Both actual output words are the original two quotient expressions from the incoming store. -/
theorem scalePairBody_results (rawLeft rawRight : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (left right : CWriteRef ctx (.unsignedWord width))
    (separate : ScalePairSeparation rawRight modulus denominator product division left right)
    (store : Store ctx) :
    let final :=
      scalePairStore rawLeft rawRight modulus denominator product division left right store
    final.read (scaleRead left) =
      scaleWordValue (store.read rawLeft) (store.read modulus) (store.read denominator) ∧
    final.read (scaleRead right) =
      scaleWordValue (store.read rawRight) (store.read modulus) (store.read denominator) := by
  let middle := scaleStore rawLeft modulus denominator product division left store
  have oldRight := scaleBody_read_other rawLeft modulus denominator product division left rawRight
    separate.productRight separate.divisionRight separate.leftRight store
  have oldModulus := scaleBody_read_other rawLeft modulus denominator product division left modulus
    separate.productModulus separate.divisionModulus separate.leftModulus store
  have oldDenominator := scaleBody_read_other rawLeft modulus denominator product division left
    denominator separate.productDenominator separate.divisionDenominator
    separate.leftDenominator store
  constructor
  · exact (scaleBody_read_other rawRight modulus denominator product division right
      (scaleRead left) separate.productLeft separate.divisionLeft separate.rightLeft middle).trans
      (scaleBody_result rawLeft modulus denominator product division left
        separate.productDenominator store)
  · have value := scaleBody_result rawRight modulus denominator product division right
      separate.productDenominator middle
    exact value.trans (by rw [oldRight, oldModulus, oldDenominator])

/-- No structural caller read outside the four actual destinations changes during either call. -/
theorem scalePairBody_read_other (rawLeft rawRight : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (left right : CWriteRef ctx (.unsignedWord width)) {shape : CShape}
    (other : CInputRef ctx shape) (productFree : product.key ∉ other.storageKeys)
    (divisionFree : division.key ∉ other.storageKeys) (leftFree : left.key ∉ other.storageKeys)
    (rightFree : right.key ∉ other.storageKeys) (store : Store ctx) :
    (scalePairStore rawLeft rawRight modulus denominator product division left right store).read
        other =
      store.read other :=
  (scaleBody_read_other rawRight modulus denominator product division right other
    productFree divisionFree rightFree _).trans
    (scaleBody_read_other rawLeft modulus denominator product division left other
      productFree divisionFree leftFree store)

end Descriptor

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The original six native instructions share both arithmetic scratch cells. -/
def scalePairBody (rawLeft rawRight : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (left right : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (scaleBody (model := model) rawLeft modulus denominator product division left)
    (scaleBody (model := model) rawRight modulus denominator product division right)

/-- Both actual triples record their values at the shared scratch stores they really use. -/
def scalePairStep (rawLeft rawRight : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (left right : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx ×
      (scalePairBody (model := model) rawLeft rawRight modulus denominator
        product division left right).Path :=
  let first := scaleStep (model := model) rawLeft modulus denominator product division left store
  let second := scaleStep (model := model) rawRight modulus denominator product division
    right first.1
  (second.1, (first.2, second.2))

/-- Both original calls preserve the complete service, history and quantum-reference state. -/
theorem scalePairBody_execute (rawLeft rawRight : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (left right : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scalePairBody (model := model) rawLeft rawRight modulus denominator product division
      left right).execute Reference state = state.mapClassical (fun entry =>
        let result := scalePairStep (model := model) rawLeft rawRight modulus denominator
          product division left right entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (scaleBody (model := model) rawLeft modulus denominator product division left)
    (scaleBody (model := model) rawRight modulus denominator product division right)
    (fun before =>
      let result := scaleStep (model := model) rawLeft modulus denominator product division
        left before.1
      ((result.1, before.2), result.2))
    (fun before =>
      let result := scaleStep (model := model) rawRight modulus denominator product division
        right before.1
      ((result.1, before.2), result.2)) ?_ ?_ Reference state).trans ?_
  · intro reference history _ before
    exact (scaleBody_execute (model := model) rawLeft modulus denominator product division left
      reference before).trans (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history _ before
    exact (scaleBody_execute (model := model) rawRight modulus denominator product division right
      reference before).trans (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Exactly the original two full-product, division and resize triples are executed. -/
theorem scalePairBody_eventTrace (rawLeft rawRight : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (left right : CWriteRef ctx (.unsignedWord width))
    (path : (scalePairBody (model := model) rawLeft rawRight modulus denominator
      product division left right).Path) :
    (scalePairBody (model := model) rawLeft rawRight modulus denominator
      product division left right).eventTrace path =
      scaleBodyEvents (model := model) width ++ scaleBodyEvents (model := model) width := by
  change (scaleBody (model := model) rawLeft modulus denominator product division left).eventTrace
      path.1 ++
    (scaleBody (model := model) rawRight modulus denominator product division right).eventTrace
      path.2 = _
  rw [scaleBody_eventTrace, scaleBody_eventTrace]

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
