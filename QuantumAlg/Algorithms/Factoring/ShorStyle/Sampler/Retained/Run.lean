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

variable {kind : ProblemKind}

/-- The actual retained circuit with its complete live-key Output. -/
def run (ctx : RuntimeCtx kind) (N : Nat) : AlgorithmRun ctx (context ctx N) (outputShape N) :=
  { code := circuit ctx N, output := output ctx N }

/-- Entering the actual run records the initial store solely as mathematical history. -/
theorem samplerRetained_run_enter (ctx : RuntimeCtx kind) (N : Nat) (Reference : Register)
    (state : ExecutionState (Store ctx) (Register.prod ctx.register Reference)) :
    (run ctx N).execute Reference state =
      (circuit ctx N).execute Reference (state.mapClassical (fun store => (store, store))) := by
  unfold AlgorithmRun.execute
  apply congrArg (fun initial : State ctx Reference (Store ctx) =>
    (circuit ctx N).execute Reference initial)
  congr 1

/-- The actual complete execution distribution retains the original caller store and source law. -/
theorem samplerRetained_run_distribution (ctx : RuntimeCtx kind) {N : Nat}
    (specification : Input N) {Reference : Register} (input : Execution.Input ctx Reference) :
    (run ctx N).executionDistribution input =
      (input.state.toPMF input.normalized).bind (fun original =>
        (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
          (fun value => (resultStore specification original value,
            (original, resultPath ctx N original value)))) := by
  let entered : State ctx Reference (Store ctx) :=
    input.state.mapClassical (fun store => (store, store))
  have enteredNormalized := input.state.mapClassical_normalized input.normalized
    (fun store => (store, store))
  have actual : (run ctx N).executionDistribution input =
      ((circuit ctx N).execute Reference entered).toPMF
        (samplerRetained_normalized ctx N Reference entered enteredNormalized) := by
    apply PMF.ext
    intro record
    have sameMass := congrArg
      (fun final : ExecutionState (run ctx N).Record
          (Register.prod (context ctx N).register Reference) =>
        ENNReal.ofReal (final.block record).mass)
      (samplerRetained_run_enter ctx N Reference input.state)
    exact (ExecutionState.toPMF_apply ((run ctx N).execute Reference input.state)
      ((run ctx N).execute_normalized input) record).trans
        (sameMass.trans (ExecutionState.toPMF_apply
          ((circuit ctx N).execute Reference entered)
          (samplerRetained_normalized ctx N Reference entered enteredNormalized) record).symm)
  refine actual.trans ((samplerRetained_toPMF ctx specification Reference entered
    enteredNormalized).trans ?_)
  let finish : Store ctx × Store ctx → PMF (run ctx N).Record := fun original =>
    (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
      (fun value => (resultStore specification original.1 value,
        (original.2, resultPath ctx N original.1 value)))
  have mapped := congrArg (fun distribution : PMF (Store ctx × Store ctx) =>
    distribution.bind finish) (ExecutionState.toPMF_mapClassical
      input.state input.normalized (fun store => (store, store)))
  exact mapped.trans (PMF.bind_map (input.state.toPMF input.normalized)
    (fun store => (store, store)) finish)

/-- The actual run's structural Output has the exact independent uniform source distribution. -/
theorem samplerRetained_run_outputDistribution (ctx : RuntimeCtx kind) {N : Nat}
    (specification : Input N) {Reference : Register} (input : Execution.Input ctx Reference) :
    (run ctx N).outputDistribution input =
      (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
        (outputValue specification) := by
  have mapped := congrArg (fun distribution : PMF (run ctx N).Record =>
    distribution.map (fun record => (output ctx N).eval record.1))
      (samplerRetained_run_distribution ctx specification input)
  refine mapped.trans ((PMF.map_bind (input.state.toPMF input.normalized)
    (fun original => (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
      (fun value => (resultStore specification original value,
        (original, resultPath ctx N original value))))
    (fun record => (output ctx N).eval record.1)).trans ?_)
  have independent (original : Store ctx) :
      ((PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
        (fun value => (resultStore specification original value,
          (original, resultPath ctx N original value)))).map
            (fun record => (output ctx N).eval record.1) =
        (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
          (outputValue specification) := by
    rw [PMF.map_comp]
    apply congrArg (fun update =>
      (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map update)
    funext value
    exact samplerRetained_output_resultStore ctx specification original value
  simp only [independent, PMF.bind_const]

/-- The actual run preserves the complete quantum-reference matrix after summing histories. -/
theorem samplerRetained_run_quantumMarginal (ctx : RuntimeCtx kind) {N : Nat}
    (specification : Input N) (Reference : Register)
    (state : ExecutionState (Store ctx) (Register.prod ctx.register Reference)) :
    ((run ctx N).finalState Reference state).quantumMarginal = state.quantumMarginal := by
  have entered := congrArg
    (fun final : ExecutionState (run ctx N).Record
        (Register.prod (context ctx N).register Reference) => final.quantumMarginal)
    (samplerRetained_run_enter ctx N Reference state)
  exact (ExecutionState.mapClassical_quantumMarginal _ Prod.fst).trans
    (entered.trans ((samplerRetained_quantumMarginal ctx specification Reference
      (state.mapClassical (fun store => (store, store)))).trans
        (ExecutionState.mapClassical_quantumMarginal state (fun store => (store, store)))))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
