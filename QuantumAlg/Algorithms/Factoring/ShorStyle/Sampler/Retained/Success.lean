/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Run

/-!
# Exact relational correctness of the actual retained sampler

The accepted result contains the actual source sample together with its
mathematically specified complete RSA parameter. Correct preparation has
probability one; this is distinct from the later probability of factoring.
The exact source distribution is separately proved from the same run.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]

/-- Independent agreement of the retained random sample and its complete mathematical parameter. -/
def correctOutput {N : Nat} (specification : Input N) (result : (outputShape N).Value) : Prop :=
  ∃ value : Fin (2 ^ residueSamplingBits N), result = outputValue specification value

/-- The actual initial store and complete structural result have the unchanged joint source law. -/
theorem samplerRetained_run_relationalDistribution (ctx : RuntimeCtx model.kind) {N : Nat}
    (specification : Input N) {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles ctx Reference) :
    (run (model := model) ctx N).relationalDistribution input =
      (input.state.toPMF input.normalized).bind (fun original =>
        (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
          (fun value => (original.1, outputValue specification value))) := by
  have mapped := congrArg (fun distribution : PMF (run (model := model) ctx N).Record =>
    distribution.map (fun record => (record.2.2.1, (output ctx N).eval record.1)))
      (samplerRetained_run_distribution ctx specification input)
  refine mapped.trans ((PMF.map_bind (input.state.toPMF input.normalized)
    (fun original => (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
      (fun value => (resultStore specification original.1 value,
        (original.2, (original.1, resultPath (model := model) ctx N original.1 value)))))
    (fun record => (record.2.2.1, (output ctx N).eval record.1))).trans ?_)
  apply congrArg (fun update => (input.state.toPMF input.normalized).bind update)
  funext original
  rw [PMF.map_comp]
  apply congrArg (fun update =>
    (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map update)
  funext value
  exact congrArg (Prod.mk original.1)
    (samplerRetained_output_resultStore ctx specification original.1 value)

/-- Every actual sampled result satisfies exact preparation, for arbitrary incoming correlations. -/
theorem samplerRetained_success (ctx : RuntimeCtx model.kind) {N : Nat}
    (specification : Input N) {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles ctx Reference) :
    (1 : ENNReal) ≤ ((run (model := model) ctx N).relationalDistribution input).toOuterMeasure
      {pair | correctOutput specification pair.2} := by
  rw [samplerRetained_run_relationalDistribution ctx specification input]
  apply le_of_eq
  symm
  apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
  intro pair supported
  obtain ⟨original, _originalSupported, sampled⟩ :=
    (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨value, _valueSupported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp sampled
  exact ⟨value, rfl⟩

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
