/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Output
import all QuantumAlg.Core.Execution.Random.Probability
import all QuantumAlg.Core.Execution.State.Preservation

/-!
# Actual probability and quantum state of retained residue sampling

Probabilities are derived from the traces of the same complete execution
blocks. The structural output has exactly the original independent finite
uniform source law, including its complete early-factor result. Summing the
classical outcomes preserves the entire caller quantum-reference matrix.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind}

/-- The actual complete sampled execution preserves normalized mass. -/
theorem samplerRetained_normalized (ctx : RuntimeCtx kind) (N : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) (normalized : state.IsNormalized) :
    ((circuit ctx N).execute Reference state).IsNormalized :=
  ((circuit ctx N).execute_mass Reference state).trans normalized

/-- The complete caller quantum state and every external reference coherence are unchanged. -/
theorem samplerRetained_quantumMarginal (ctx : RuntimeCtx kind) {N : Nat} (input : Input N)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    ((circuit ctx N).execute Reference state).quantumMarginal = state.quantumMarginal := by
  have actual := congrArg
    (fun final : State (context ctx N) Reference (History × (circuit ctx N).Path) =>
      final.quantumMarginal) (samplerRetained_execute ctx input Reference state)
  exact actual.trans ((ExecutionState.mapClassical_quantumMarginal _ _).trans
    (uniformChoice_quantumMarginal state ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩))

/-- Every actual complete execution record has the unchanged independent uniform source law. -/
theorem samplerRetained_toPMF (ctx : RuntimeCtx kind) {N : Nat} (input : Input N)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) (normalized : state.IsNormalized) :
    ((circuit ctx N).execute Reference state).toPMF
        (samplerRetained_normalized ctx N Reference state normalized) =
      (state.toPMF normalized).bind (fun original =>
        (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
          (fun value => (resultStore input original.1 value,
            (original.2, resultPath ctx N original.1 value)))) := by
  let sampled := uniformChoice state
    (⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩ : ℕ+)
  have sampledNormalized := uniformChoice_normalized state normalized
    ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩
  let update : (Store ctx × History) × Fin (2 ^ residueSamplingBits N) →
      Store (context ctx N) × (History × (circuit ctx N).Path) := fun entry =>
    (resultStore input entry.1.1 entry.2, (entry.1.2, resultPath ctx N entry.1.1 entry.2))
  have actual :
      ((circuit ctx N).execute Reference state).toPMF
          (samplerRetained_normalized ctx N Reference state normalized) =
        (sampled.mapClassical update).toPMF
          (sampled.mapClassical_normalized sampledNormalized update) := by
    apply PMF.ext
    intro record
    simp only [ExecutionState.toPMF_apply]
    exact congrArg
      (fun final : State (context ctx N) Reference (History × (circuit ctx N).Path) =>
        ENNReal.ofReal (final.block record).mass)
      (samplerRetained_execute ctx input Reference state)
  refine actual.trans ((ExecutionState.toPMF_mapClassical
    sampled sampledNormalized update).trans ?_)
  have sampledLaw := congrArg (fun distribution => distribution.map update)
    (uniformChoice_toPMF state normalized
      ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩)
  refine sampledLaw.trans ((PMF.map_bind (state.toPMF normalized)
    (fun original => (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
      (fun sample => (original, sample))) update).trans ?_)
  apply congrArg (fun continuation => (state.toPMF normalized).bind continuation)
  funext original
  exact PMF.map_comp (fun sample => (original, sample))
    (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))) update

/-- The complete mathematical result store reads the independently specified source value. -/
theorem samplerRetained_output_resultStore (ctx : RuntimeCtx kind) {N : Nat}
    (input : Input N) (store : Store ctx) (value : Fin (2 ^ residueSamplingBits N)) :
    (output ctx N).eval (resultStore input store value) = outputValue input value :=
  (congrArg (output ctx N).eval (samplerRetained_result_store input store value).symm).trans
    (samplerRetained_output_outcome ctx input (pushStore N store) value)

/-- Reading the actual complete Output gives exactly the original uniform source distribution. -/
theorem samplerRetained_output_toPMF (ctx : RuntimeCtx kind) {N : Nat} (input : Input N)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) (normalized : state.IsNormalized) :
    (((circuit ctx N).execute Reference state).toPMF
        (samplerRetained_normalized ctx N Reference state normalized)).map
          (fun record => (output ctx N).eval record.1) =
      (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map (outputValue input) := by
  rw [samplerRetained_toPMF ctx input Reference state normalized, PMF.map_bind]
  have independent (original : Store ctx × History) :
      ((PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
        (fun value => (resultStore input original.1 value,
          (original.2, resultPath ctx N original.1 value)))).map
            (fun record => (output ctx N).eval record.1) =
        (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map (outputValue input) := by
    rw [PMF.map_comp]
    apply congrArg (fun update =>
      (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map update)
    funext value
    exact samplerRetained_output_resultStore ctx input original.1 value
  simp only [independent, PMF.bind_const]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
