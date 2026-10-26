/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Value

/-!
# Actual-store correctness of paid nearest scaling

Scratch separation protects the original order and power-of-two denominator.
Every returned value comes from the actual preceding instruction; the final
store read is the exact finite-word expression proved free of overflow.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest

open Execution
open RawRecovery.Native (scaleRead scaleProductOp)

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Storage disjointness needed by nearest scaling's actual intermediate reads. -/
structure ScaleSeparation (refs : ScaleRefs ctx width) : Prop where
  productOrder : refs.product.key ∉ refs.order.storageKeys
  productDenominator : refs.product.key ∉ refs.denominator.storageKeys
  halfOrder : refs.half.key ∉ refs.order.storageKeys
  halfDenominator : refs.half.key ∉ refs.denominator.storageKeys
  halfProduct : refs.half.key ∉ (scaleRead refs.product).storageKeys
  divisionOrder : refs.division.key ∉ refs.order.storageKeys

/-- The seven actual classical store updates, in chronological order. -/
def scaleStore (refs : ScaleRefs ctx width) (store : Store ctx) : Store ctx :=
  ((((((store.applyOp (scaleProductOp refs.raw refs.order refs.product)).applyOp
    refs.halfResizeOp).applyOp refs.halfShiftOp).applyOp refs.roundOp).applyOp
      refs.divideOp).applyOp refs.reduceOp).applyOp refs.finishOp

/-- The final existing output cell contains the exact finite-word nearest result. -/
lemma scaleStore_result (refs : ScaleRefs ctx width) (separate : ScaleSeparation refs)
    (store : Store ctx) :
    (scaleStore refs store).read (scaleRead refs.output) =
      scaleWordValue (store.read refs.raw) (store.read refs.order)
        (store.read refs.denominator) := by
  let first := store.applyOp (scaleProductOp refs.raw refs.order refs.product)
  let second := first.applyOp refs.halfResizeOp
  let third := second.applyOp refs.halfShiftOp
  let fourth := third.applyOp refs.roundOp
  let fifth := fourth.applyOp refs.divideOp
  let sixth := fifth.applyOp refs.reduceOp
  have denominatorFirst : first.read refs.denominator = store.read refs.denominator :=
    Store.read_applyOp_of_not_mem_storageKeys store
      (scaleProductOp refs.raw refs.order refs.product) refs.denominator separate.productDenominator
  have denominatorFourth : fourth.read refs.denominator = store.read refs.denominator := by
    calc
      _ = third.read refs.denominator :=
        Store.read_applyOp_of_not_mem_storageKeys third refs.roundOp refs.denominator
          separate.productDenominator
      _ = second.read refs.denominator :=
        Store.read_applyOp_of_not_mem_storageKeys second refs.halfShiftOp refs.denominator
          separate.halfDenominator
      _ = first.read refs.denominator :=
        Store.read_applyOp_of_not_mem_storageKeys first refs.halfResizeOp refs.denominator
          separate.halfDenominator
      _ = _ := denominatorFirst
  have orderFifth : fifth.read refs.order = store.read refs.order := by
    calc
      _ = fourth.read refs.order :=
        Store.read_applyOp_of_not_mem_storageKeys fourth refs.divideOp refs.order
          separate.divisionOrder
      _ = third.read refs.order :=
        Store.read_applyOp_of_not_mem_storageKeys third refs.roundOp refs.order
          separate.productOrder
      _ = second.read refs.order :=
        Store.read_applyOp_of_not_mem_storageKeys second refs.halfShiftOp refs.order
          separate.halfOrder
      _ = first.read refs.order :=
        Store.read_applyOp_of_not_mem_storageKeys first refs.halfResizeOp refs.order
          separate.halfOrder
      _ = _ := Store.read_applyOp_of_not_mem_storageKeys store
        (scaleProductOp refs.raw refs.order refs.product) refs.order separate.productOrder
  have productThird : third.read (scaleRead refs.product) =
      CShape.mulFull width (width + 1)
        (.product (store.read refs.raw) (store.read refs.order)) := by
    calc
      _ = second.read (scaleRead refs.product) :=
        Store.read_applyOp_of_not_mem_storageKeys second refs.halfShiftOp
          (scaleRead refs.product) separate.halfProduct
      _ = first.read (scaleRead refs.product) :=
        Store.read_applyOp_of_not_mem_storageKeys first refs.halfResizeOp
          (scaleRead refs.product) separate.halfProduct
      _ = _ := Store.read_applyOp_output store (scaleProductOp refs.raw refs.order refs.product)
  have halfSecond : second.read (scaleRead refs.half) =
      CShape.wordResize (width + (width + 1)) (store.read refs.denominator) := by
    have result := Store.read_applyOp_output first refs.halfResizeOp
    change second.read (scaleRead refs.half) =
      CShape.wordResize (width + (width + 1)) (first.read refs.denominator) at result
    exact result.trans (congrArg _ denominatorFirst)
  have halfThird : third.read (scaleRead refs.half) =
      CShape.wordShiftRight (width + (width + 1))
        (CShape.wordResize (width + (width + 1)) (store.read refs.denominator)) := by
    have result := Store.read_applyOp_output second refs.halfShiftOp
    change third.read (scaleRead refs.half) =
      CShape.wordShiftRight (width + (width + 1))
        (second.read (scaleRead refs.half)) at result
    exact result.trans (congrArg _ halfSecond)
  have productFourth := Store.read_applyOp_output third refs.roundOp
  change fourth.read (scaleRead refs.product) =
    CShape.wordOfNat (width + (width + 1))
      ((third.read (scaleRead refs.product)).toNat +
        (third.read (scaleRead refs.half)).toNat) at productFourth
  rw [productThird, halfThird] at productFourth
  have divisionFifth := Store.read_applyOp_output fourth refs.divideOp
  change fifth.read (scaleRead refs.division) =
    CShape.divRem (width + (width + 1)) (width + 1)
      (.product (fourth.read (scaleRead refs.product))
        (fourth.read refs.denominator)) at divisionFifth
  rw [productFourth, denominatorFourth] at divisionFifth
  have divisionSixth := Store.read_applyOp_output fifth refs.reduceOp
  change sixth.read (scaleRead refs.division) =
    CShape.divRem (width + (width + 1)) (width + 1)
      (.product (fifth.read (scaleRead refs.division)).first
        (fifth.read refs.order)) at divisionSixth
  rw [divisionFifth, orderFifth] at divisionSixth
  have result := Store.read_applyOp_output sixth refs.finishOp
  change (scaleStore refs store).read (scaleRead refs.output) =
    CShape.wordResize width (sixth.read (scaleRead refs.division)).second at result
  rw [divisionSixth] at result
  exact result

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The actual returned path's store is exactly the seven declared updates. -/
lemma scaleStep_store (refs : ScaleRefs ctx width) (store : Store ctx) :
    (scaleStep (model := model) refs store).1 = scaleStore refs store := rfl

/-- Every nearest instruction preserves reads outside its four actual destination cells. -/
lemma scaleStep_read_other (refs : ScaleRefs ctx width) {shape : CShape}
    (other : CInputRef ctx shape)
    (productFree : refs.product.key ∉ other.storageKeys)
    (halfFree : refs.half.key ∉ other.storageKeys)
    (divisionFree : refs.division.key ∉ other.storageKeys)
    (outputFree : refs.output.key ∉ other.storageKeys) (store : Store ctx) :
    (scaleStep (model := model) refs store).1.read other = store.read other := by
  rw [scaleStep_store]
  unfold scaleStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ refs.finishOp other outputFree,
    Store.read_applyOp_of_not_mem_storageKeys _ refs.reduceOp other divisionFree,
    Store.read_applyOp_of_not_mem_storageKeys _ refs.divideOp other divisionFree,
    Store.read_applyOp_of_not_mem_storageKeys _ refs.roundOp other productFree,
    Store.read_applyOp_of_not_mem_storageKeys _ refs.halfShiftOp other halfFree,
    Store.read_applyOp_of_not_mem_storageKeys _ refs.halfResizeOp other halfFree]
  exact Store.read_applyOp_of_not_mem_storageKeys store
    (scaleProductOp refs.raw refs.order refs.product) other productFree

/-- Actual nearest scaling computes the mathematical nearest residue with no
intermediate overflow and no assumption about incoming scratch contents. -/
lemma scaleStep_nearest (refs : ScaleRefs ctx width) (separate : ScaleSeparation refs)
    (store : Store ctx) (spec : ClassicalAlgorithms.Modular.ModulusSpec width)
    (orderValue : (store.read refs.order).toNat = spec.modulus)
    (powerValue : (store.read refs.denominator).toNat = 2 ^ width) :
    ((scaleStep (model := model) refs store).1.read (scaleRead refs.output)).toNat =
      NearestResidue.quotient ((store.read refs.raw).toNat * spec.modulus) (2 ^ width) %
        spec.modulus := by
  rw [scaleStep_store, scaleStore_result refs separate store]
  have orderPositive : 0 < (store.read refs.order).toNat := by
    rw [orderValue]
    exact ClassicalAlgorithms.Modular.modulusSpec_modulus_pos spec
  have orderBound : (store.read refs.order).toNat ≤ 2 ^ width := by
    rw [orderValue]
    exact spec.le_capacity
  rw [scaleWordValue_toNat _ _ _ orderPositive orderBound powerValue, orderValue]

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest
