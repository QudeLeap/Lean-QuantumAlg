/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.AlgorithmRun.Borrowed
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Whole-run borrowed restoration without borrowed quantum wires

The actual run records the original Store as mathematical history. The
circuit's joint borrowed-state restoration transports through that recording,
retaining all classical and external Reference correlations.
-/

namespace QuantumAlg.AlgorithmRun

noncomputable section

open Execution

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

/-- The complete actual run preserves the borrowed state and Reference jointly. -/
lemma restoresBorrowed_of_noBorrowedQuantum {model : ExecutionModel}
    {environment : model.Environment} {allowAllocation : Bool}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (actual : AlgorithmRun model pre post shape allowAllocation)
    (noBorrowed : pre.borrowedQuantumWires = [])
    {Reference : Register} (supplied : OracleInput model.classicalOracles pre Reference) :
    actual.RestoresBorrowed environment supplied := by
  let recorded := supplied.state.mapClassical (fun value => (value.1, (value.2, value.1)))
  have restored := actual.code.borrowedRestored_of_noBorrowedQuantum (environment := environment)
    noBorrowed Reference recorded
  change observeBorrowedAfter actual.code Reference
      (actual.code.execute environment Reference recorded) = observeBorrowed Reference
        supplied.state
  have observed := observeBorrowed_mapClassical supplied.state
    (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
  have recordedObservation : observeBorrowed Reference recorded =
      observeBorrowed Reference supplied.state := by
    convert observed using 1
    apply congrArg (fun state : State pre Reference (model.HiddenState × Store pre) =>
      observeBorrowed Reference state)
    exact ExecutionState.executionState_mapClassical_congr supplied.state rfl
  exact restored.trans recordedObservation

end

end QuantumAlg.AlgorithmRun
