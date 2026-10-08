/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Support
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Execution.State.Promise

/-!
# Comparing complete weighted readout states

Equal output probabilities determine the complete readout state when both
executions preserve the same normalized quantum/reference density in every
output block, including blocks of zero probability.
-/

namespace QuantumAlg.AlgorithmRun

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem readout_block_mass {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (program : AlgorithmRun model pre post shape) {Reference : Register}
    (original : OracleInput model.classicalOracles pre Reference)
    (value : shape.Value) :
    ENNReal.ofReal
        ((((program.finalState Reference original.state).mapClassical
          program.output.eval).block value).mass) =
      program.outputDistribution original value := by
  have mapped := congrArg (fun distribution : PMF shape.Value => distribution value)
    (ExecutionState.toPMF_mapClassical
      (program.execute Reference original.state)
      (program.execute_normalized original)
      (fun record => program.output.eval record.1))
  rw [ExecutionState.toPMF_apply] at mapped
  rw [← AlgorithmRun.finalState_readout program Reference original.state] at mapped
  change _ = program.outputDistribution original value at mapped
  exact mapped

/-- Equal output PMFs and a shared blockwise state promise determine the
entire weighted classical-quantum-reference readout state. -/
theorem readoutState_eq_of_distribution_and_promise
    {model : ExecutionModel} {pre post : RuntimeCtx model.kind} {shape : CShape}
    (left right : AlgorithmRun model pre post shape) {Reference : Register}
    (original : OracleInput model.classicalOracles pre Reference)
    (target : DensityOperator (Register.prod post.register Reference))
    (normalized : target.IsNormalized)
    (leftPromise : ∀ value,
      (StatePromise.mixed target normalized).Holds
        (((left.finalState Reference original.state).mapClassical left.output.eval).block value))
    (rightPromise : ∀ value,
      (StatePromise.mixed target normalized).Holds
        (((right.finalState Reference original.state).mapClassical right.output.eval).block value))
    (sameDistribution : left.outputDistribution original = right.outputDistribution original) :
    (left.finalState Reference original.state).mapClassical left.output.eval =
      (right.finalState Reference original.state).mapClassical right.output.eval := by
  let leftState := (left.finalState Reference original.state).mapClassical left.output.eval
  let rightState := (right.finalState Reference original.state).mapClassical right.output.eval
  change leftState = rightState
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  have sameMass :
      (leftState.block value).mass = (rightState.block value).mass := by
    apply (ENNReal.ofReal_eq_ofReal_iff
      (ExecutionState.block _ _).mass_nonneg
      (ExecutionState.block _ _).mass_nonneg).mp
    exact (readout_block_mass left original value).trans
      ((congrArg (fun distribution : PMF shape.Value => distribution value)
        sameDistribution).trans (readout_block_mass right original value).symm)
  exact (leftPromise value).trans (by rw [sameMass]; exact (rightPromise value).symm)

end

end QuantumAlg.AlgorithmRun
