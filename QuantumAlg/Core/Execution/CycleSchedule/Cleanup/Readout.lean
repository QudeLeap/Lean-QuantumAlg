/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.CycleSchedule.Cleanup.Sequence
import all QuantumAlg.Core.Execution.Classical.Support
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.Input.Oracle

/-!
# Fixed physical reset state at the actual algorithm readout

The output read is a finite grouping of the original complete execution
records. No path, hidden service state or incoming reference is discarded
before the pure-state promise is established.
-/

namespace QuantumAlg.Circuit.RestartCleanup

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution

/-- The actual final-state readout retains the chosen pure owned quantum seed
on every output value and for every finite weighted input state. -/
def ReadoutPure {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (program : AlgorithmRun model pre post shape)
    (seed : post.quantumLayout.SelectedBasis post.borrowedSelectionᶜ) : Prop :=
  ∀ (Reference : Register)
    (input : ExecutionState (Store pre × model.HiddenState)
      (Register.prod pre.register Reference)) (value : shape.Value),
    (StatePromise.pure (NormalizedVector.ket seed)).Holds
      (DensityOperator.observeSelection post.quantumLayout post.borrowedSelectionᶜ Reference
        (((program.finalState Reference input).mapClassical program.output.eval).block value))

/-- A specified physical reset establishes that readout law for the same
executed run; the initial store is retained as history before grouping. -/
theorem readoutPure {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (program : AlgorithmRun model pre post shape)
    (seed : post.quantumLayout.SelectedBasis post.borrowedSelectionᶜ)
    (fixed : Circuit.ReinitializedAt program.code seed) :
    ReadoutPure program seed := by
  unfold ReadoutPure
  intro Reference input value
  let entered := input.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  have direct := groupedPureAt fixed Reference entered
    (fun record => program.output.eval record.1) value
  have readout := AlgorithmRun.finalState_readout program Reference input
  change (program.finalState Reference input).mapClassical program.output.eval =
    (program.code.execute Reference entered).mapClassical
      (fun record => program.output.eval record.1) at readout
  rw [readout]
  exact direct

/-- The named actual readout law satisfies the corresponding independently
chosen marginal pure-state requirement on the same algorithm. -/
theorem stateRequirement {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (program : AlgorithmRun model pre post shape)
    (seed : post.quantumLayout.SelectedBasis post.borrowedSelectionᶜ)
    (fixed : Circuit.ReinitializedAt program.code seed)
    {Reference : Register}
    (input : OracleInput model.classicalOracles pre Reference) :
    (StateRequirement.marginal post.borrowedSelectionᶜ program.output.result
      (fun _ _ => StatePromise.pure (NormalizedVector.ket seed))).Holds
        input.caller (program.finalState Reference input.state) := by
  apply (StateRequirement.marginal_pure_holds_iff post.borrowedSelectionᶜ
    program.output.result (NormalizedVector.ket seed) input.caller
    (program.finalState Reference input.state)).2
  exact (readoutPure program seed fixed) Reference input.state

end

end QuantumAlg.Circuit.RestartCleanup
