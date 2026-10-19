/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.Borrowed.Classical

/-!
# Original borrowed values beneath retained measurement cells

Dropping only the newly retained store heads exposes the original store.
Every structural lifted read and the complete borrowed observation agree
with that store. This is an exact coordinate projection, not an execution
or a claim that a retained cell has been released.
-/

namespace QuantumAlg.Execution

noncomputable section

namespace Store

/-- An original structural operand reads the old store beneath a retained head. -/
lemma retainedTail_read {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (store : Store (ctx.addRetained key shape fresh)) {inputShape : CShape}
    (input : CInputRef ctx inputShape) :
    (Store.mk store.cells.2).read input =
      store.read (input.underRetained key shape fresh) := by
  induction input with
  | storage => rfl
  | product first second firstIH secondIH =>
      exact congrArg₂ CShape.Value.product firstIH secondIH
  | fixedVector entries entriesIH =>
      exact congrArg CShape.Value.fixedVector (funext entriesIH)
  | first source sourceIH => exact congrArg CShape.Value.first sourceIH
  | second source sourceIH => exact congrArg CShape.Value.second sourceIH
  | vectorGet source index sourceIH => exact congrArg (fun value => value.get index) sourceIH
  | bitsGet source index sourceIH => exact congrArg (fun value => value.bitGet index) sourceIH
  | wordBitGet source index sourceIH =>
      exact congrArg (fun value => value.wordBitGet index) sourceIH

end Store

namespace MeasurementCells

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Expose only the original store under the actual retained measurement-cell heads. -/
def originalStore (dimension : ℕ+) :
    (count : Nat) → Store (context ctx dimension count) → Store ctx
  | 0, store => store
  | count + 1, store => originalStore dimension count ⟨store.cells.2⟩

/-- Every original structural read agrees exactly after dropping those retained heads. -/
lemma originalStore_read (dimension : ℕ+) (count : Nat)
    (store : Store (context ctx dimension count)) {shape : CShape}
    (input : CInputRef ctx shape) :
    (originalStore dimension count store).read input =
      store.read (liftInput dimension input count) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [originalStore, induction]
      exact Store.retainedTail_read _ _ _ store _

/-- Retained measurement heads preserve the complete actual borrowed observation. -/
lemma originalStore_borrowed (dimension : ℕ+) (count : Nat)
    (store : Store (context ctx dimension count)) :
    HEq store.readBorrowedClassical
      (originalStore dimension count store).readBorrowedClassical := by
  induction count with
  | zero => rfl
  | succ count induction =>
      change HEq (Store.mk store.cells.2).readBorrowedClassical
        (originalStore dimension count ⟨store.cells.2⟩).readBorrowedClassical
      exact induction _

end MeasurementCells

end

end QuantumAlg.Execution
