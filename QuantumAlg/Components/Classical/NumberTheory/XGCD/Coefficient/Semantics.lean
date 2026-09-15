/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Coefficient.Step
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Exact store recurrence for native coefficient updates

The equations hold at every word width, with arbitrary scratch contents.
Separation concerns the actual cell identities of the internal circuit;
the lexical state construction establishes it when assembling the engine.
The quotient is consumed before any write and may share an input cell.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem coefficientOp_preserves_cell {input output : CShape}
    (op : ClassicalOp input output ctx ctx) (other : CWriteRef ctx (.unsignedWord width))
    (different : op.outputRef.key ≠ other.key) (store : Store ctx) :
    (store.applyOp op).read (coefficientRead other) = store.read (coefficientRead other) :=
  Store.read_write_other store op.outputRef other.toCStorageRef _ different

private theorem coefficientProduct_read (quotient : CInputRef ctx (.unsignedWord width))
    (first product : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (store.applyOp (coefficientProductOp quotient first product)).read
        (coefficientRead product) =
      Resource.WordBinaryOpcode.eval .mulLow width
        (.product (store.read quotient) (store.read (coefficientRead first))) :=
  Store.read_applyOp_output store (coefficientProductOp quotient first product)

private theorem coefficientSubtract_read
    (second product updated : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (store.applyOp (coefficientSubtractOp second product updated)).read
        (coefficientRead updated) =
      Resource.WordBinaryOpcode.eval .sub width
        (.product (store.read (coefficientRead second)) (store.read (coefficientRead product))) :=
  Store.read_applyOp_output store (coefficientSubtractOp second product updated)

private theorem coefficientCopy_read (source target : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    (store.applyOp (coefficientCopyOp source target)).read (coefficientRead target) =
      store.read (coefficientRead source) :=
  Store.read_applyOp_output store (coefficientCopyOp source target)

/-- Every structural read outside the four written cells is preserved exactly. -/
theorem xgcdCoefficientUpdate_read_other (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width)) {observed : CShape}
    (other : CInputRef ctx observed)
    (firstFree : first.key ∉ other.storageKeys) (secondFree : second.key ∉ other.storageKeys)
    (productFree : product.key ∉ other.storageKeys) (updatedFree : updated.key ∉ other.storageKeys)
    (store : Store ctx) :
    (coefficientUpdateStore quotient first second product updated store).read other =
      store.read other := by
  unfold coefficientUpdateStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (coefficientCopyOp updated first) other firstFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (coefficientCopyOp first second) other secondFree,
    Store.read_applyOp_of_not_mem_storageKeys _
      (coefficientSubtractOp second product updated) other updatedFree,
    Store.read_applyOp_of_not_mem_storageKeys _
      (coefficientProductOp quotient first product) other productFree]

/-- The two final words satisfy the exact modular coefficient recurrence and rotation. -/
theorem xgcdCoefficientUpdate_store_values (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width))
    (firstSecond : first.key ≠ second.key)
    (productFirst : product.key ≠ first.key) (productSecond : product.key ≠ second.key)
    (updatedFirst : updated.key ≠ first.key) (secondUpdated : second.key ≠ updated.key)
    (store : Store ctx) :
    let final := coefficientUpdateStore quotient first second product updated store
    final.read (coefficientRead first) =
        Resource.WordBinaryOpcode.eval .sub width
          (.product (store.read (coefficientRead second))
            (Resource.WordBinaryOpcode.eval .mulLow width
              (.product (store.read quotient) (store.read (coefficientRead first))))) ∧
      final.read (coefficientRead second) = store.read (coefficientRead first) := by
  let multiplied := store.applyOp (coefficientProductOp quotient first product)
  let subtracted := multiplied.applyOp (coefficientSubtractOp second product updated)
  let rotated := subtracted.applyOp (coefficientCopyOp first second)
  have multipliedFirst : multiplied.read (coefficientRead first) =
      store.read (coefficientRead first) :=
    coefficientOp_preserves_cell (coefficientProductOp quotient first product)
      first productFirst store
  have multipliedSecond : multiplied.read (coefficientRead second) =
      store.read (coefficientRead second) :=
    coefficientOp_preserves_cell (coefficientProductOp quotient first product)
      second productSecond store
  have subtractedFirst : subtracted.read (coefficientRead first) =
      store.read (coefficientRead first) := by
    rw [coefficientOp_preserves_cell (coefficientSubtractOp second product updated)
      first updatedFirst multiplied, multipliedFirst]
  have rotatedUpdated : rotated.read (coefficientRead updated) =
      subtracted.read (coefficientRead updated) :=
    coefficientOp_preserves_cell (coefficientCopyOp first second)
      updated secondUpdated subtracted
  dsimp only
  constructor
  · change (rotated.applyOp (coefficientCopyOp updated first)).read (coefficientRead first) = _
    rw [coefficientCopy_read, rotatedUpdated, coefficientSubtract_read,
      multipliedSecond, coefficientProduct_read]
  · change (rotated.applyOp (coefficientCopyOp updated first)).read (coefficientRead second) = _
    rw [coefficientOp_preserves_cell (coefficientCopyOp updated first) second firstSecond rotated,
      coefficientCopy_read, subtractedFirst]

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD
