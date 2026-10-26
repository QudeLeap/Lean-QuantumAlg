/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Forward.Values

/-!
# Protected reads through the actual forward batch record

Only the existing D array and product word can change. In particular a
separately loaded modulus and the protected coordinate/source cells retain
their exact original values for every subsequent arithmetic instruction.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame

open Execution Modular.NativePower

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}

/-- The actual prefix snapshot and multiply preserve every read outside their true outputs. -/
lemma forwardRecord_read_other (frame : BatchFrame ctx width length) (index : Fin length)
    {shape : CShape} (observed : CInputRef ctx shape)
    (prefixFree : frame.prefixes.key ∉ observed.storageKeys)
    (productFree : frame.work.product.key ∉ observed.storageKeys) (store : Store ctx) :
    (frame.forwardRecord (model := model) index store).1.read observed = store.read observed := by
  exact (nativePower_scopedMultiply_read_other (model := model)
    (wordRead frame.work.product) (rowRead frame.denominators index) frame.modulus
    frame.work.product observed productFree
    (store.applyOp (rowWriteOp frame.prefixes index (wordRead frame.work.product)))).trans
    (Store.read_applyOp_of_not_mem_storageKeys store
      (rowWriteOp frame.prefixes index (wordRead frame.work.product)) observed prefixFree)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame
