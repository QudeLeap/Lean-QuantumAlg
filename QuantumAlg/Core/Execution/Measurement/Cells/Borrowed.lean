/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.Classical.Retained.Read
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
