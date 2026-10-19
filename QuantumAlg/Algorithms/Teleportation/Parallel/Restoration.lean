/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Teleportation.Parallel.Construction
import all QuantumAlg.Algorithms.Teleportation.Parallel.Geometry
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Borrowed-state restoration of the native teleportation execution

The supplied input and resource systems have input roles; only the actual
measurement cells have auxiliary roles. Native gates, measurements and
feedback preserve the complete external-reference observation through the
recorded original store [dW19, qcnotes.tex:790,802,804].
-/

namespace QuantumAlg.QuantumTeleportation.Parallel.Restoration

noncomputable section

open QuantumAlg.Execution

attribute [local instance] Classical.decEq

private lemma cells_noBorrowedQuantum (ctx : RuntimeCtx .quantum)
    (empty : ctx.borrowedQuantumWires = []) (count : Nat) :
    (MeasurementCells.context ctx 2 count).borrowedQuantumWires = [] := by
  induction count with
  | zero => exact empty
  | succ count ih =>
      rw [MeasurementCells.context, RuntimeCtx.borrowedQuantumWires_addRetained]
      exact ih

lemma noBorrowedQuantum (count : Nat) : (context count).borrowedQuantumWires = [] :=
  cells_noBorrowedQuantum (quantumContext count) rfl (count * 2)

/-- The run retains every external-reference entry while recording its real initial store. -/
lemma borrowed (environment : model.Environment) (count : Nat) {Reference : Register}
    (input : OracleInput .empty (context count) Reference) :
    ((algorithm count).run.RestoresBorrowed environment) input := by
  let recorded : State (context count) Reference (model.HiddenState × Store (context count)) :=
    input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  have restored := (code count).borrowedRestored_of_noBorrowedQuantum
    environment (noBorrowedQuantum count) Reference recorded
  have observed := observeBorrowed_mapClassical input.state
    (fun entry => (entry.1, (entry.2, entry.1))) (fun _ => rfl)
  have recordedObservation : observeBorrowed Reference recorded =
      observeBorrowed Reference input.state := by
    convert observed using 1
    apply congrArg (fun state : State (context count) Reference
      (model.HiddenState × Store (context count)) => observeBorrowed Reference state)
    exact ExecutionState.executionState_mapClassical_congr input.state rfl
  change observeBorrowedAfter (code count) Reference
    (((code count).execute environment) Reference recorded) = observeBorrowed Reference input.state
  exact restored.trans recordedObservation

end

end QuantumAlg.QuantumTeleportation.Parallel.Restoration
