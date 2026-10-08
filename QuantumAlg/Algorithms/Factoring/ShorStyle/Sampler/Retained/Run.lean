/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Probability
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# One complete run of the native retained residue sampler

The run contains the actual circuit and its complete structural Output.
Its probabilities retain the original input store as mathematical history;
that history introduces no physical storage. The same run has the exact
independent source distribution and preserves the full caller/reference state.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]

/-- The actual retained circuit with its complete live-key Output. -/
def run (ctx : RuntimeCtx model.kind) (N : Nat) :
    AlgorithmRun model ctx (context ctx N) (outputShape N) :=
  { code := circuit (model := model) ctx N, output := output ctx N }

/-- Entering the actual run records the initial store solely as mathematical history. -/
theorem samplerRetained_run_enter (ctx : RuntimeCtx model.kind) (N : Nat) (Reference : Register)
    (state : ExecutionState (Store ctx × model.HiddenState)
      (Register.prod ctx.register Reference)) :
    (run (model := model) ctx N).execute Reference state =
      (circuit (model := model) ctx N).execute Reference
        (state.mapClassical (fun value => (value.1, (value.2, value.1)))) := by
  unfold AlgorithmRun.execute
  apply congrArg (fun initial : State ctx Reference (model.HiddenState × Store ctx) =>
    (circuit (model := model) ctx N).execute Reference initial)
  congr 1

/-- The actual complete execution distribution retains the original caller store and source law. -/
theorem samplerRetained_run_distribution (ctx : RuntimeCtx model.kind) {N : Nat}
    (specification : Input N) {Reference : Register}
        (input : Execution.OracleInput model.classicalOracles ctx Reference) :
    (run (model := model) ctx N).executionDistribution input =
      (input.state.toPMF input.normalized).bind (fun original =>
        (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
          (fun value => (resultStore specification original.1 value,
            (original.2, (original.1, resultPath (model := model) ctx N original.1 value))))) := by
  let entered : State ctx Reference (model.HiddenState × Store ctx) :=
    input.state.mapClassical (fun value => (value.1, (value.2, value.1)))
  have enteredNormalized := input.state.mapClassical_normalized input.normalized
    (fun value => (value.1, (value.2, value.1)))
  have actual : (run (model := model) ctx N).executionDistribution input =
      ((circuit (model := model) ctx N).execute Reference entered).toPMF
        (samplerRetained_normalized (model := model)
            ctx N Reference entered enteredNormalized) := by
    apply PMF.ext
    intro record
    have sameMass := congrArg
      (fun final : ExecutionState (run (model := model) ctx N).Record
          (Register.prod (context ctx N).register Reference) =>
        ENNReal.ofReal (final.block record).mass)
      (samplerRetained_run_enter (model := model) ctx N Reference input.state)
    exact (ExecutionState.toPMF_apply ((run (model := model) ctx N).execute Reference input.state)
      ((run (model := model) ctx N).execute_normalized input) record).trans
        (sameMass.trans (ExecutionState.toPMF_apply
          ((circuit (model := model) ctx N).execute Reference entered)
          (samplerRetained_normalized (model := model)
              ctx N Reference entered enteredNormalized) record).symm)
  refine actual.trans ((samplerRetained_toPMF ctx specification Reference entered
    enteredNormalized).trans ?_)
  let finish : Store ctx × (model.HiddenState × Store ctx) → PMF (run (model := model)
      ctx N).Record := fun original =>
    (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
      (fun value => (resultStore specification original.1 value,
        (original.2.1, (original.2.2, resultPath (model := model) ctx N original.1 value))))
  have mapped := congrArg (fun distribution : PMF (Store ctx × (model.HiddenState × Store ctx)) =>
    distribution.bind finish) (ExecutionState.toPMF_mapClassical
      input.state input.normalized (fun value => (value.1, (value.2, value.1))))
  exact mapped.trans (PMF.bind_map (input.state.toPMF input.normalized)
    (fun value => (value.1, (value.2, value.1))) finish)

/-- The actual run's structural Output has the exact independent uniform source distribution. -/
theorem samplerRetained_run_outputDistribution (ctx : RuntimeCtx model.kind) {N : Nat}
    (specification : Input N) {Reference : Register}
        (input : Execution.OracleInput model.classicalOracles ctx Reference) :
    (run (model := model) ctx N).outputDistribution input =
      (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
        (outputValue specification) := by
  have mapped := congrArg (fun distribution : PMF (run (model := model) ctx N).Record =>
    distribution.map (fun record => (output ctx N).eval record.1))
      (samplerRetained_run_distribution (model := model) ctx specification input)
  refine mapped.trans ((PMF.map_bind (input.state.toPMF input.normalized)
    (fun original => (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
      (fun value => (resultStore specification original.1 value,
        (original.2, (original.1, resultPath (model := model) ctx N original.1 value)))))
    (fun record => (output ctx N).eval record.1)).trans ?_)
  have independent (original : Store ctx × model.HiddenState) :
      ((PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
        (fun value => (resultStore specification original.1 value,
          (original.2, (original.1, resultPath (model := model) ctx N original.1 value))))).map
            (fun record => (output ctx N).eval record.1) =
        (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
          (outputValue specification) := by
    rw [PMF.map_comp]
    apply congrArg (fun update =>
      (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map update)
    funext value
    exact samplerRetained_output_resultStore ctx specification original.1 value
  refine (congrArg (fun continuation =>
    (input.state.toPMF input.normalized).bind continuation) (funext independent)).trans ?_
  exact PMF.bind_const _ _

/-- The actual run preserves the complete quantum-reference matrix after summing histories. -/
theorem samplerRetained_run_quantumMarginal (ctx : RuntimeCtx model.kind) {N : Nat}
    (specification : Input N) (Reference : Register)
    (state : ExecutionState (Store ctx × model.HiddenState)
      (Register.prod ctx.register Reference)) :
    ((run (model := model)
        ctx N).finalState Reference state).quantumMarginal = state.quantumMarginal := by
  have entered := congrArg
    (fun final : ExecutionState (run (model := model) ctx N).Record
        (Register.prod (context ctx N).register Reference) => final.quantumMarginal)
    (samplerRetained_run_enter (model := model) ctx N Reference state)
  exact (ExecutionState.mapClassical_quantumMarginal _ Prod.fst).trans
    (entered.trans ((samplerRetained_quantumMarginal ctx specification Reference
      (state.mapClassical (fun value => (value.1, (value.2, value.1))))).trans
        (ExecutionState.mapClassical_quantumMarginal state (fun value =>
            (value.1, (value.2, value.1))))))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
