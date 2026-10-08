/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Semantics
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Borrowed.Classical

/-!
# Structural reads and complete borrowed restoration of selection

Only the actual two scratch cells and two persistent latches can be written.
All other structural reads are preserved, and intrinsic write ownership
preserves borrowed values even when writable selector cells alias. Together
with the exact state equation this restores their complete joint observation
with every borrowed quantum system and external reference.
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

/-- A structural read outside all four written keys keeps its complete original value. -/
theorem firstAccepted_read_other (inputs : Inputs ctx width) (refs : Refs ctx width)
    {shape : CShape} (other : CInputRef ctx shape)
    (availableFree : refs.available.key ∉ other.storageKeys)
    (takeFree : refs.take.key ∉ other.storageKeys)
    (acceptedFree : refs.accepted.key ∉ other.storageKeys)
    (selectedFree : refs.selected.key ∉ other.storageKeys) (store : Store ctx) :
    (step (model := model) inputs refs store).1.read other = store.read other := by
  have decisionRead : (decisionStore inputs refs store).read other = store.read other :=
    (Store.read_applyOp_of_not_mem_storageKeys _ (takeOp inputs refs) other takeFree).trans
      (Store.read_applyOp_of_not_mem_storageKeys _ (availableOp refs) other availableFree)
  rw [firstAccepted_step_store]
  dsimp only
  split
  · exact ((Store.read_applyOp_of_not_mem_storageKeys _ (acceptedCopyOp refs)
      other acceptedFree).trans
      (Store.read_applyOp_of_not_mem_storageKeys _ (selectedCopyOp inputs refs)
        other selectedFree)).trans decisionRead
  · exact decisionRead

/-- The actual first-accepted step preserves every borrowed classical value. -/
theorem firstAccepted_step_borrowed_values (inputs : Inputs ctx width) (refs : Refs ctx width)
    (store : Store ctx) :
    (step (model := model) inputs refs store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  rw [firstAccepted_step_store]
  dsimp only
  split
  · simp only [copyStore, Store.readBorrowedClassical_applyOp, decisionStore]
  · simp only [decisionStore, Store.readBorrowedClassical_applyOp]

/-- Every actual selector execution restores the joint borrowed interface on every reference. -/
theorem firstAccepted_borrowedRestored (inputs : Inputs ctx width) (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (circuit (model := model) inputs refs).BorrowedRestored Reference state
      ((circuit (model := model) inputs refs).execute Reference state) := by
  rw [Circuit.BorrowedRestored, observeBorrowedAfter_sameContext, firstAccepted_execute]
  refine Eq.trans ?_ (observeBorrowed_mapClassical (ctx := ctx) (Reference := Reference)
    (H := model.HiddenState × History)
    (K := model.HiddenState × (History × (circuit (model := model) inputs refs).Path)) state
    (fun entry =>
      let result := step (model := model) inputs refs entry.1
      (result.1, (entry.2.1, (entry.2.2, result.2))))
    (fun entry => firstAccepted_step_borrowed_values inputs refs entry.1))
  congr 1
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.ClassicalRoutines.FirstAccepted
