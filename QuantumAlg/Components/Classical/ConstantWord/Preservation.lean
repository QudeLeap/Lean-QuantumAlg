/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.ConstantWord.Semantics
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Borrowed restoration of the literal constant-word loader

Every real shift and selected increment uses an intrinsically writable cell.
Their store update preserves the complete borrowed classical value. Combined
with the actual full-state equation, this restores every borrowed system
jointly with any external reference.
-/

namespace QuantumAlg.ClassicalRoutines.ConstantWord

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

private theorem append_borrowed (output : CWriteRef ctx (.unsignedWord width))
    (bit : Bool) (store : Store ctx) :
    (appendStep (model := model) output bit store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  cases bit <;> simp only [appendStep, BitWord.instructionStep, Store.readBorrowedClassical_applyOp]

/-- The actual literal-bit fold preserves every borrowed classical value. -/
theorem constantWord_foldStep_borrowed_values (output : CWriteRef ctx (.unsignedWord width))
    (bits : List Bool) (store : Store ctx) :
    (foldStep (model := model) output bits store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  induction bits generalizing store with
  | nil => rfl
  | cons bit remaining ih =>
      change (foldStep (model := model) output remaining
        (appendStep (model := model) output bit store).1).1.readBorrowedClassical = _
      rw [ih, append_borrowed]

/-- The actual fold restores all borrowed classical and quantum systems with every reference. -/
theorem constantWord_fold_borrowedRestored (output : CWriteRef ctx (.unsignedWord width))
    (bits : List Bool) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (fold (model := model) output bits).BorrowedRestored Reference state
      ((fold (model := model) output bits).execute Reference state) := by
  rw [Circuit.BorrowedRestored, observeBorrowedAfter_sameContext, constantWord_fold_execute]
  refine Eq.trans ?_ (observeBorrowed_mapClassical (ctx := ctx) (Reference := Reference)
    (H := model.HiddenState × History)
    (K := model.HiddenState × (History × (fold (model := model) output bits).Path)) state
    (fun entry =>
      let result := foldStep (model := model) output bits entry.1
      (result.1, (entry.2.1, (entry.2.2, result.2))))
    (fun entry => constantWord_foldStep_borrowed_values (model := model) output bits entry.1))
  exact congrArg (fun result => observeBorrowed (ctx := ctx) (Reference := Reference) result)
    (ExecutionState.executionState_mapClassical_congr _ rfl)

end

end QuantumAlg.ClassicalRoutines.ConstantWord
