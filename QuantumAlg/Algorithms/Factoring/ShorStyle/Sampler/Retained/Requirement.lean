/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Run
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.MarginalLaws

/-!
# Independent complete caller-state promise for retained sampling

The target is the incoming full quantum-reference density, observed on every
actual caller system. It is independent of the sampler program and its resource
account. The real retained allocations add only classical cells, so no quantum
system is omitted, created or traced out by this complete layout selection.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind}

private def incomingTarget (ctx : RuntimeCtx kind) (N : Nat) (Reference : Register)
    (input : Execution.Input ctx Reference) :
    DensityOperator (Register.prod
      ((context ctx N).quantumLayout.selectedRegister Finset.univ) Reference) :=
  DensityOperator.observeSelectionWithReference (context ctx N).quantumLayout
    Finset.univ Reference input.state.quantumMarginal

private theorem incomingTarget_normalized (ctx : RuntimeCtx kind) (N : Nat)
    (Reference : Register) (input : Execution.Input ctx Reference) :
    (incomingTarget ctx N Reference input).IsNormalized :=
  (DensityOperator.observeSelectionWithReference_mass (context ctx N).quantumLayout
    Finset.univ Reference input.state.quantumMarginal).trans
      ((ExecutionState.quantumMarginal_mass input.state).trans input.normalized)

/-- Preserve the complete incoming quantum-reference density on the full actual output layout. -/
def requirement (ctx : RuntimeCtx kind) (N : Nat) : StateRequirement ctx (context ctx N) :=
  .jointReference Finset.univ .unit fun Reference input _ =>
    .mixed (incomingTarget ctx N Reference input) (incomingTarget_normalized ctx N Reference input)

/-- Actual retained sampling satisfies the independent full-state promise for every reference. -/
theorem samplerRetainedRequirement_holds (ctx : RuntimeCtx kind) {N : Nat}
    (specification : Input N) {Reference : Register} (input : Execution.Input ctx Reference) :
    (requirement ctx N).Holds input ((run ctx N).finalState Reference input.state) := by
  intro value
  cases value with
  | unit =>
      let result := (run ctx N).finalState Reference input.state
      have actual : result.quantumMarginal = input.state.quantumMarginal :=
        samplerRetained_run_quantumMarginal ctx specification Reference input.state
      have observed := congrArg
        (fun density : DensityOperator (Register.prod (context ctx N).register Reference) =>
          DensityOperator.observeSelectionWithReference (context ctx N).quantumLayout
            Finset.univ Reference density)
        ((ExecutionState.executionState_mapClassical_const_block result CShape.Value.unit).trans
          actual)
      have targetHolds :
          (StatePromise.mixed (incomingTarget ctx N Reference input)
            (incomingTarget_normalized ctx N Reference input)).Holds
              (incomingTarget ctx N Reference input) := by
        change (incomingTarget ctx N Reference input).matrix =
          ((incomingTarget ctx N Reference input).mass : ℝ) •
            (incomingTarget ctx N Reference input).matrix
        rw [incomingTarget_normalized]
        simp only [one_smul]
      exact (congrArg
        (StatePromise.mixed (incomingTarget ctx N Reference input)
          (incomingTarget_normalized ctx N Reference input)).Holds observed).mpr targetHolds

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
