/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Execution
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Complete actual scalar-write form of the scoped native multiply

The exact returned caller Store is determined by the computed finite-word
result and every retained other read. Both real arithmetic scratch cells
are released. This equality keeps aliases and the original actual modulus.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open Execution Modular.NativePower

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The existing paid scoped multiply returns precisely one actual caller-cell overwrite. -/
lemma scopedMultiplyStep_store (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (scopedMultiplyStep (model := model) left right modulus output store).1 =
      store.write output
        (multiplyValue (store.read left) (store.read right) (store.read modulus)) := by
  apply Store.store_eq_write_of_read_frame
  · exact nativePower_scopedMultiply_result left right modulus output store
  · intro shape other different
    exact nativePower_scopedMultiply_read_other left right modulus output (.storage other)
      (by simpa only [CInputRef.storageKeys, List.mem_singleton] using different) store

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
