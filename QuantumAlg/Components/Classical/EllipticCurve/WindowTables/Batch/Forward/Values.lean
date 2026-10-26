/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Execution
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.Separation

/-!
# Exact actual prefix-pass cell values

The actual D-row write snapshots the old product before multiplication.
Every original C row survives the step. Its resulting scalar is the real
finite-word multiply/reduction of the original product and denominator,
with the same original stored modulus.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame

open Execution Modular.NativePower

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : BatchFrame ctx width length)

/-- Every C entry survives the actual prefix write and scalar multiplication. -/
lemma forwardRecord_read_denominator (index observed : Fin length) (store : Store ctx) :
    ((frame.forwardRecord (model := model) index store).1).read
      (rowRead frame.denominators observed) = store.read (rowRead frame.denominators observed) := by
  change ((scopedMultiplyStep (model := model) (wordRead frame.work.product)
    (rowRead frame.denominators index) frame.modulus frame.work.product
    (store.applyOp (rowWriteOp frame.prefixes index (wordRead frame.work.product)))).1).read
      (rowRead frame.denominators observed) = _
  rw [nativePower_scopedMultiply_read_other _ _ _ _ _
    (by
      change frame.work.product.key ∉ [frame.denominators.key]
      simpa only [List.mem_singleton] using
        word_array_key_ne frame.work.product frame.denominators)]
  apply Store.read_applyOp_of_not_mem_storageKeys
  change frame.prefixes.key ∉ [frame.denominators.key]
  simpa only [List.mem_singleton] using Ne.symm frame.separate

/-- The selected D row retains exactly the product read before its actual native multiply. -/
lemma forwardRecord_read_prefix (index : Fin length) (store : Store ctx) :
    ((frame.forwardRecord (model := model) index store).1).read (rowRead frame.prefixes index) =
      store.read (wordRead frame.work.product) := by
  change ((scopedMultiplyStep (model := model) (wordRead frame.work.product)
    (rowRead frame.denominators index) frame.modulus frame.work.product
    (store.applyOp (rowWriteOp frame.prefixes index (wordRead frame.work.product)))).1).read
      (rowRead frame.prefixes index) = _
  rw [nativePower_scopedMultiply_read_other _ _ _ _ _
    (by
      change frame.work.product.key ∉ [frame.prefixes.key]
      simpa only [List.mem_singleton] using word_array_key_ne frame.work.product frame.prefixes)]
  exact rowWrite_read_same frame.prefixes index (wordRead frame.work.product) store

/-- Every earlier/later D row survives this different original prefix-row overwrite. -/
lemma forwardRecord_read_other_prefix (index observed : Fin length) (different : observed ≠ index)
    (store : Store ctx) :
    ((frame.forwardRecord (model := model) index store).1).read (rowRead frame.prefixes observed) =
      store.read (rowRead frame.prefixes observed) := by
  change ((scopedMultiplyStep (model := model) (wordRead frame.work.product)
    (rowRead frame.denominators index) frame.modulus frame.work.product
    (store.applyOp (rowWriteOp frame.prefixes index (wordRead frame.work.product)))).1).read
      (rowRead frame.prefixes observed) = _
  rw [nativePower_scopedMultiply_read_other _ _ _ _ _
    (by
      change frame.work.product.key ∉ [frame.prefixes.key]
      simpa only [List.mem_singleton] using word_array_key_ne frame.work.product frame.prefixes)]
  exact rowWrite_read_other frame.prefixes index (wordRead frame.work.product) store observed
    different

/-- The real product uses the original running value and original C entry, including aliases. -/
lemma forwardRecord_read_product (index : Fin length)
    (modulusFree : frame.prefixes.key ∉ frame.modulus.storageKeys) (store : Store ctx) :
    ((frame.forwardRecord (model := model) index store).1).read (wordRead frame.work.product) =
      multiplyValue (store.read (wordRead frame.work.product))
        (store.read (rowRead frame.denominators index)) (store.read frame.modulus) := by
  change ((scopedMultiplyStep (model := model) (wordRead frame.work.product)
    (rowRead frame.denominators index) frame.modulus frame.work.product
    (store.applyOp (rowWriteOp frame.prefixes index (wordRead frame.work.product)))).1).read
      (wordRead frame.work.product) = _
  rw [nativePower_scopedMultiply_result]
  have productStored := rowWrite_read_word frame.prefixes index (wordRead frame.work.product)
    frame.work.product store
  change (store.applyOp (rowWriteOp frame.prefixes index (wordRead frame.work.product))).read
    (wordRead frame.work.product) = store.read (wordRead frame.work.product) at productStored
  rw [productStored]
  rw [Store.read_applyOp_of_not_mem_storageKeys _
    (rowWriteOp frame.prefixes index (wordRead frame.work.product))
    (rowRead frame.denominators index)
    (by
      change frame.prefixes.key ∉ [frame.denominators.key]
      simpa only [List.mem_singleton] using Ne.symm frame.separate)]
  rw [Store.read_applyOp_of_not_mem_storageKeys _
    (rowWriteOp frame.prefixes index (wordRead frame.work.product)) frame.modulus modulusFree]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame
