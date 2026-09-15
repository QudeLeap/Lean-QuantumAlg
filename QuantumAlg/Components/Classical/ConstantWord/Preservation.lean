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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem append_borrowed (output : CWriteRef ctx (.unsignedWord width))
    (bit : Bool) (store : Store ctx) :
    (appendStep output bit store).1.readBorrowedClassical = store.readBorrowedClassical := by
  cases bit <;> simp only [appendStep, Store.readBorrowedClassical_applyOp]

/-- The actual literal-bit fold preserves every borrowed classical value. -/
theorem constantWord_foldStep_borrowed_values (output : CWriteRef ctx (.unsignedWord width))
    (bits : List Bool) (store : Store ctx) :
    (foldStep output bits store).1.readBorrowedClassical = store.readBorrowedClassical := by
  induction bits generalizing store with
  | nil => rfl
  | cons bit remaining ih =>
      change (foldStep output remaining
        (appendStep output bit store).1).1.readBorrowedClassical = _
      rw [ih, append_borrowed]

/-- The actual fold restores all borrowed classical and quantum systems with every reference. -/
theorem constantWord_fold_borrowedRestored (output : CWriteRef ctx (.unsignedWord width))
    (bits : List Bool) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (fold output bits).BorrowedRestored Reference state
      ((fold output bits).execute Reference state) := by
  rw [Circuit.BorrowedRestored, observeBorrowedAfter_sameContext, constantWord_fold_execute]
  refine Eq.trans ?_ (observeBorrowed_mapClassical (ctx := ctx) (Reference := Reference)
    (H := History) (K := History × (fold output bits).Path) state
    (fun entry => ((foldStep output bits entry.1).1, (entry.2, (foldStep output bits entry.1).2)))
    (fun entry => constantWord_foldStep_borrowed_values output bits entry.1))
  congr 1
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.ClassicalRoutines.ConstantWord
