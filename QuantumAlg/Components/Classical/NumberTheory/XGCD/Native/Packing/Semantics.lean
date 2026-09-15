/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Packing
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Correctness
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Store

/-!
# Actual public XGCD packing values

The semantic result is the original right-nested encoding of the real gcd
word and the two genuinely resized and packed coefficient words. Internal
scratch protects the still-needed source words and the first signed result.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.NumberTheory

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The nominal value of the three actual raw words under the original public packing. -/
def packedRawValue (gcd : CShape.Word width)
    (left right : CShape.Word (PureXGCD.executionCoefficientWidth width)) :
    CShape.Value (XGCDOutputShape width) :=
  .product gcd (.product
    (CShape.packBoundedSignedWord (coefficientWidth width)
      (CShape.wordResize (coefficientWidth width) left))
    (CShape.packBoundedSignedWord (coefficientWidth width)
      (CShape.wordResize (coefficientWidth width) right)))

/-- The actual body preserves all reads outside its three scratch cells and final output. -/
theorem xgcdNativePackingBody_read_other (outputs : RawOutputs ctx width)
    (raw : CWriteRef ctx (.unsignedWord (coefficientWidth width)))
    (left right : CWriteRef ctx (SignedShape (coefficientWidth width)))
    (result : CWriteRef ctx (XGCDOutputShape width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (rawFree : raw.key ∉ other.storageKeys) (leftFree : left.key ∉ other.storageKeys)
    (rightFree : right.key ∉ other.storageKeys) (resultFree : result.key ∉ other.storageKeys) :
    (packingBodyStore outputs raw left right result store).read other = store.read other := by
  unfold packingBodyStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (.packProduct ctx
      (.product (GCD.cellRead outputs.gcd)
        (.product (GCD.cellRead left) (GCD.cellRead right))) result) other resultFree,
    Store.read_applyOp_of_not_mem_storageKeys _
      (.packBoundedSignedWord (coefficientWidth width) ctx (GCD.cellRead raw) right)
      other rightFree,
    Store.read_applyOp_of_not_mem_storageKeys _
      (.wordResize (PureXGCD.executionCoefficientWidth width) (coefficientWidth width) ctx
        (GCD.cellRead outputs.rightCoefficient) raw) other rawFree,
    Store.read_applyOp_of_not_mem_storageKeys _
      (.packBoundedSignedWord (coefficientWidth width) ctx (GCD.cellRead raw) left) other leftFree,
    Store.read_applyOp_of_not_mem_storageKeys _
      (.wordResize (PureXGCD.executionCoefficientWidth width) (coefficientWidth width) ctx
        (GCD.cellRead outputs.leftCoefficient) raw) other rawFree]

/-- Original protected source reads make the five actual operations return the packed raw value. -/
theorem xgcdNativePackingBody_result (outputs : RawOutputs ctx width)
    (raw : CWriteRef ctx (.unsignedWord (coefficientWidth width)))
    (left right : CWriteRef ctx (SignedShape (coefficientWidth width)))
    (result : CWriteRef ctx (XGCDOutputShape width)) (store : Store ctx)
    (rawGcd : raw.key ∉ (GCD.cellRead outputs.gcd).storageKeys)
    (leftGcd : left.key ∉ (GCD.cellRead outputs.gcd).storageKeys)
    (rightGcd : right.key ∉ (GCD.cellRead outputs.gcd).storageKeys)
    (rawRight : raw.key ∉ (GCD.cellRead outputs.rightCoefficient).storageKeys)
    (leftRight : left.key ∉ (GCD.cellRead outputs.rightCoefficient).storageKeys)
    (rawLeft : raw.key ∉ (GCD.cellRead left).storageKeys)
    (rightLeft : right.key ∉ (GCD.cellRead left).storageKeys) :
    (packingBodyStore outputs raw left right result store).read (GCD.cellRead result) =
      packedRawValue (store.read (GCD.cellRead outputs.gcd))
        (store.read (GCD.cellRead outputs.leftCoefficient))
        (store.read (GCD.cellRead outputs.rightCoefficient)) := by
  let resizeLeft := ClassicalOp.wordResize (PureXGCD.executionCoefficientWidth width)
    (coefficientWidth width) ctx (GCD.cellRead outputs.leftCoefficient) raw
  let packLeft := ClassicalOp.packBoundedSignedWord (coefficientWidth width) ctx
    (GCD.cellRead raw) left
  let resizeRight := ClassicalOp.wordResize (PureXGCD.executionCoefficientWidth width)
    (coefficientWidth width) ctx (GCD.cellRead outputs.rightCoefficient) raw
  let packRight := ClassicalOp.packBoundedSignedWord (coefficientWidth width) ctx
    (GCD.cellRead raw) right
  let first := store.applyOp resizeLeft
  let second := first.applyOp packLeft
  let third := second.applyOp resizeRight
  let fourth := third.applyOp packRight
  have firstRaw : first.read (GCD.cellRead raw) =
      CShape.wordResize (coefficientWidth width)
        (store.read (GCD.cellRead outputs.leftCoefficient)) :=
    Store.read_applyOp_output store resizeLeft
  have secondLeft : second.read (GCD.cellRead left) =
      CShape.packBoundedSignedWord (coefficientWidth width) (first.read (GCD.cellRead raw)) :=
    Store.read_applyOp_output first packLeft
  have secondRight : second.read (GCD.cellRead outputs.rightCoefficient) =
      store.read (GCD.cellRead outputs.rightCoefficient) :=
    (Store.read_applyOp_of_not_mem_storageKeys first packLeft
      (GCD.cellRead outputs.rightCoefficient) leftRight).trans
      (Store.read_applyOp_of_not_mem_storageKeys store resizeLeft
        (GCD.cellRead outputs.rightCoefficient) rawRight)
  have thirdRaw : third.read (GCD.cellRead raw) =
      CShape.wordResize (coefficientWidth width)
        (second.read (GCD.cellRead outputs.rightCoefficient)) :=
    Store.read_applyOp_output second resizeRight
  have fourthRight : fourth.read (GCD.cellRead right) =
      CShape.packBoundedSignedWord (coefficientWidth width) (third.read (GCD.cellRead raw)) :=
    Store.read_applyOp_output third packRight
  have fourthLeft : fourth.read (GCD.cellRead left) = second.read (GCD.cellRead left) :=
    (Store.read_applyOp_of_not_mem_storageKeys third packRight (GCD.cellRead left) rightLeft).trans
      (Store.read_applyOp_of_not_mem_storageKeys second resizeRight (GCD.cellRead left) rawLeft)
  have fourthGcd : fourth.read (GCD.cellRead outputs.gcd) = store.read (GCD.cellRead outputs.gcd) :=
    (Store.read_applyOp_of_not_mem_storageKeys third packRight
      (GCD.cellRead outputs.gcd) rightGcd).trans
      ((Store.read_applyOp_of_not_mem_storageKeys second resizeRight
        (GCD.cellRead outputs.gcd) rawGcd).trans
        ((Store.read_applyOp_of_not_mem_storageKeys first packLeft
          (GCD.cellRead outputs.gcd) leftGcd).trans
          (Store.read_applyOp_of_not_mem_storageKeys store resizeLeft
            (GCD.cellRead outputs.gcd) rawGcd)))
  have packed : (fourth.applyOp (.packProduct ctx
      (.product (GCD.cellRead outputs.gcd)
        (.product (GCD.cellRead left) (GCD.cellRead right))) result)).read (GCD.cellRead result) =
      .product (fourth.read (GCD.cellRead outputs.gcd))
        (.product (fourth.read (GCD.cellRead left)) (fourth.read (GCD.cellRead right))) :=
    Store.read_applyOp_output fourth (.packProduct ctx
      (.product (GCD.cellRead outputs.gcd)
        (.product (GCD.cellRead left) (GCD.cellRead right))) result)
  change (fourth.applyOp (.packProduct ctx
    (.product (GCD.cellRead outputs.gcd)
      (.product (GCD.cellRead left) (GCD.cellRead right))) result)).read (GCD.cellRead result) = _
  rw [packed, fourthGcd, fourthLeft, secondLeft, firstRaw, fourthRight, thirdRaw, secondRight]
  rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
