/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Reverse.Values

/-!
# Structural reads outside the actual reverse batch outputs

The two real scoped multiplies and the final C-row overwrite retain every
other structurally supplied read. This includes all protected coordinate
arrays and the actual widened modulus used by the next chronological step.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame

open Execution Modular.NativePower

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}

/-- Only the declared existing C array, inverse word and temporary word may change. -/
lemma reverseRecord_read_other (frame : BatchFrame ctx width length) (index : Fin length)
    {shape : CShape} (observed : CInputRef ctx shape)
    (denominatorFree : frame.denominators.key ∉ observed.storageKeys)
    (inverseFree : frame.work.inverse.key ∉ observed.storageKeys)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys) (store : Store ctx) :
    (frame.reverseRecord (model := model) index store).1.read observed = store.read observed := by
  let first := (scopedMultiplyStep (model := model) (wordRead frame.work.inverse)
    (rowRead frame.prefixes index) frame.modulus frame.work.temporary store).1
  let second := (scopedMultiplyStep (model := model) (wordRead frame.work.inverse)
    (rowRead frame.denominators index) frame.modulus frame.work.inverse first).1
  exact (Store.read_applyOp_of_not_mem_storageKeys second
    (rowWriteOp frame.denominators index (wordRead frame.work.temporary)) observed
    denominatorFree).trans
    ((nativePower_scopedMultiply_read_other (model := model) (wordRead frame.work.inverse)
      (rowRead frame.denominators index) frame.modulus frame.work.inverse observed inverseFree
      first).trans
      (nativePower_scopedMultiply_read_other (model := model) (wordRead frame.work.inverse)
        (rowRead frame.prefixes index) frame.modulus frame.work.temporary observed temporaryFree
        store))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame
