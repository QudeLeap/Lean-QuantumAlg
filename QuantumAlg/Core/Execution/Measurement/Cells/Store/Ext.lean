/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Cells

/-!
# Complete stores when retained measurement cells are the only classical data

On an original context with a unique classical store, reads of the actual
retained cells determine the complete extended store. Quantum entries still
carry only presence markers; this statement neither observes nor identifies
their quantum state [dW19, qcnotes.tex:5381,5394,5405].
-/

namespace QuantumAlg.Execution.MeasurementCells

/-- All newly retained finite-cell reads determine the complete store over a unique old store. -/
lemma store_eq_of_reference_reads {kind : ProblemKind} (ctx : RuntimeCtx kind)
    [Subsingleton (Store ctx)] (dimension : ℕ+) (count : Nat)
    (first second : Store (context ctx dimension count))
    (same : ∀ index : Fin count,
      first.read (.storage (reference ctx dimension count index).toCStorageRef) =
        second.read (.storage (reference ctx dimension count index).toCStorageRef)) :
    first = second := by
  induction count with
  | zero => exact Subsingleton.elim (α := Store ctx) first second
  | succ count ih =>
      apply congrArg Store.mk
      change (first.cells.1, first.cells.2) = (second.cells.1, second.cells.2)
      apply Prod.ext
      · exact same 0
      · let oldFirst : Store (context ctx dimension count) := ⟨first.cells.2⟩
        let oldSecond : Store (context ctx dimension count) := ⟨second.cells.2⟩
        have old := ih oldFirst oldSecond (fun index => same index.succ)
        exact congrArg Store.cells old

end QuantumAlg.Execution.MeasurementCells
