/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.ConstantWord.Semantics
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Complete Store returned by actual constant loading

All original shifts and selected increments retain their certified path. The
complete returned Store is the one target write, independently of its prior
contents and without any caller initialization premise.
-/

namespace QuantumAlg.ClassicalRoutines.ConstantWord

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The real width-many shift and increment sequence changes exactly its actual target word. -/
lemma constantWord_fold_store (output : CWriteRef ctx (.unsignedWord width))
    (constant : Nat) (store : Store ctx) :
    (foldStep (model := model) output (List.ofFn (constantBits width constant)) store).1 =
      store.write output (CShape.wordOfNat width constant) := by
  apply Store.store_eq_write_of_read_frame
  · have actual := constantWord_read (model := model) output constant store
    change (foldStep (model := model) output (List.ofFn (constantBits width constant)) store).1.read
      (targetRead output) = _
    cases value : (foldStep (model := model) output
      (List.ofFn (constantBits width constant)) store).1.read
      (targetRead output) with
    | unsignedWord result =>
        apply congrArg CShape.Value.unsignedWord
        apply Fin.ext
        rw [value] at actual
        exact actual
  · intro shape input different
    exact constantWord_fold_read_other (model := model) output _ (.storage input)
      (by simpa [CInputRef.storageKeys] using different) store

end

end QuantumAlg.ClassicalRoutines.ConstantWord
