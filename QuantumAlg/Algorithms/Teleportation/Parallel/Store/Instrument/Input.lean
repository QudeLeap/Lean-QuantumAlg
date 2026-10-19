/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Teleportation.Parallel.BellResource
import all QuantumAlg.Algorithms.Teleportation.Parallel.Construction
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# The original local Bell promise for the actual recorded input

Recording the original classical store changes no joint quantum/reference
entry. The original local promise for the supplied Bell bank therefore
applies directly to that same recorded execution input [dW19,
qcnotes.tex:785,809]. No conditional state or new admission condition is used.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel.StoreInstrument

noncomputable section

open Execution

/-- The actual initial history recording leaves the complete caller quantum marginal unchanged. -/
lemma recorded_quantumMarginal (count : Nat) {Reference : Register}
    [DecidableEq (Store (context count) × (model.HiddenState × Store (context count)))]
    (input : OracleInput .empty (context count) Reference) :
    (input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))).quantumMarginal =
      input.caller.state.quantumMarginal :=
  (ExecutionState.mapClassical_quantumMarginal input.state
    (fun entry => (entry.1, (entry.2, entry.1)))).trans
      (OracleInput.oracleInput_caller_quantumMarginal input).symm

/-- Only the original locally supplied Bell marginal is required for the recorded input. -/
lemma recorded_bellPromise (count : Nat) {Reference : Register}
    [DecidableEq (Store (context count) × (model.HiddenState × Store (context count)))]
    (input : OracleInput .empty (context count) Reference)
    (admitted : localBellMarginal count input.caller.localState.quantumMarginal =
      DensityOperator.ofPure (bellBank count)) :
    localBellMarginal count
        (DensityOperator.marginalLeft
          (input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))).quantumMarginal) =
      DensityOperator.ofPure (bellBank count) := by
  rw [recorded_quantumMarginal, ← Input.localState_quantumMarginal]
  exact admitted

end

end QuantumAlg.QuantumTeleportation.Parallel.StoreInstrument
