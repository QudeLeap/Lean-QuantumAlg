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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original six native instructions share both arithmetic scratch cells. -/
def scalePairBody (rawLeft rawRight : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (left right : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (scaleBody rawLeft modulus denominator product division left)
    (scaleBody rawRight modulus denominator product division right)

/-- The second scaling starts in the actual first scaling's returned store. -/
def scalePairStore (rawLeft rawRight : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (left right : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  scaleStore rawRight modulus denominator product division right
    (scaleStore rawLeft modulus denominator product division left store)

/-- Both original scaling calls retain the complete quantum-reference state and actual paths. -/
theorem scalePairBody_execute (rawLeft rawRight : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (left right : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (scalePairBody rawLeft rawRight modulus denominator product division left right).execute
      Reference state = state.mapClassical (fun entry =>
        (scalePairStore rawLeft rawRight modulus denominator product division left right entry.1,
          (entry.2, (((), ((), ())), ((), ((), ())))))) := by
  refine (Circuit.execute_seq_mapClassical
    (scaleBody rawLeft modulus denominator product division left)
    (scaleBody rawRight modulus denominator product division right)
    (fun before => (scaleStore rawLeft modulus denominator product division left before,
      ((), ((), ()))))
    (fun before => (scaleStore rawRight modulus denominator product division right before,
      ((), ((), ()))))
    (fun reference {_} _ before => by
      refine (scaleBody_execute rawLeft modulus denominator product division left
        reference before).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (fun reference {_} _ before => by
      refine (scaleBody_execute rawRight modulus denominator product division right
        reference before).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

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

/-- Exactly the original two full-product, division and resize triples are executed. -/
theorem scalePairBody_eventTrace (rawLeft rawRight : CInputRef ctx (.unsignedWord width))
    (modulus denominator : CInputRef ctx (.unsignedWord (width + 1)))
    (product : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (division : CWriteRef ctx (scaleDivisionShape width))
    (left right : CWriteRef ctx (.unsignedWord width))
    (path : (scalePairBody rawLeft rawRight modulus denominator product division left right).Path) :
    (scalePairBody rawLeft rawRight modulus denominator product division left right).eventTrace
        path =
      scaleBodyEvents kind width ++ scaleBodyEvents kind width := rfl

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
