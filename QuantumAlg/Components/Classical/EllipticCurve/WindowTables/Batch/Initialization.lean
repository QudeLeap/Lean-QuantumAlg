/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.Separation
import all QuantumAlg.Components.Classical.Modular.NativePower.Multiply
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Actual batch initializer values

The original paid word-resize instruction copies the original supplied one
word without narrowing loss. It changes only the product scalar. All real
array cells and every protected structural read retain their exact values.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame

open Execution Modular.NativePower

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- The actual Store update of the original paid batch initializer. -/
def initializeStore (frame : BatchFrame ctx width length) (store : Store ctx) : Store ctx :=
  store.applyOp (.wordResize width width ctx frame.one frame.work.product)

/-- Copying the supplied scalar word retains all its original bits exactly. -/
lemma initializeStore_read_product (frame : BatchFrame ctx width length) (store : Store ctx) :
    ((frame.initializeStore store).read (wordRead frame.work.product)).toNat =
      (store.read frame.one).toNat := by
  have written := Store.read_applyOp_output store
    (ClassicalOp.wordResize width width ctx frame.one frame.work.product)
  change (frame.initializeStore store).read (wordRead frame.work.product) =
    CShape.wordResize width (store.read frame.one) at written
  rw [written]
  exact ClassicalOp.eval_wordResize_exact width width ctx frame.one frame.work.product
    (store.read frame.one) (store.read frame.one).toNat_lt

/-- Only the existing product scalar may change during the real initializer. -/
lemma initializeStore_read_other (frame : BatchFrame ctx width length)
    {shape : CShape} (observed : CInputRef ctx shape)
    (separate : frame.work.product.key ∉ observed.storageKeys) (store : Store ctx) :
    (frame.initializeStore store).read observed = store.read observed :=
  Store.read_applyOp_of_not_mem_storageKeys store
    (ClassicalOp.wordResize width width ctx frame.one frame.work.product) observed separate

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame
