/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Step
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Exact deterministic specializations of declared classical execution

These equations apply when the selected declaration itself has a proved point
distribution. They retain the actual store update and mathematical history,
including the next oracle state. The equality hypothesis concerns the native declaration
or supplied service
interpretation; no extra evaluator is admitted by the instruction syntax.
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {History : Type} [Fintype History]

open scoped Classical in
/-- A proved point-valued native declaration gives this exact complete store map. -/
public lemma nativeStep_of_pure {model : ClassicalOpModel}
    (application : model.Application ctx)
    (compute : (model.inputShape application.token).Value →
      (model.outputShape application.token).Value)
    (declared : ∀ value, model.evaluate application.token value = PMF.pure (compute value))
    (state : State ctx Reference History) :
    nativeStep application state = state.mapClassical (fun entry =>
      let result := compute (entry.1.read application.input)
      (entry.1.write application.output result, (entry.2, result))) := by
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  rw [nativeStep_block_matrix]
  change _ = ∑ entry : Store ctx × History,
    if (entry.1.write application.output (compute (entry.1.read application.input)),
        (entry.2, compute (entry.1.read application.input))) = result then
      (state.block entry).matrix else 0
  simp_rw [declared]
  apply Finset.sum_congr rfl
  intro entry _
  rw [Finset.sum_eq_single (compute (entry.1.read application.input))]
  · simp only [PMF.pure_apply_self, ENNReal.toReal_one, one_smul]
  · intro other _ different
    simp only [PMF.pure_apply, different, if_false, ENNReal.toReal_zero, zero_smul, ite_self]
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

open scoped Classical in
/-- A deterministic service transition updates its persistent state and visible result together. -/
public lemma queryStep_of_pure {model : ClassicalOracleModel}
    (application : model.Application ctx) (environment : model.Interpretation)
    (compute : model.HiddenState → (model.inputShape application.query).Value →
      model.HiddenState × (model.outputShape application.query).Value)
    (declared : ∀ hidden value,
      model.transition environment application.query hidden value = PMF.pure (compute hidden value))
    (state : State ctx Reference (model.HiddenState × History)) :
    queryStep environment application state = state.mapClassical (fun entry =>
      let result := compute entry.2.1 (entry.1.read application.input)
      (entry.1.write application.output result.2, (result.1, (entry.2.2, result.2)))) := by
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  rw [queryStep_block_matrix]
  change _ = ∑ entry : Store ctx × (model.HiddenState × History),
    if (entry.1.write application.output
          (compute entry.2.1 (entry.1.read application.input)).2,
        ((compute entry.2.1 (entry.1.read application.input)).1,
          (entry.2.2, (compute entry.2.1 (entry.1.read application.input)).2))) = result then
      (state.block entry).matrix else 0
  simp_rw [declared]
  apply Finset.sum_congr rfl
  intro entry _
  rw [Finset.sum_eq_single (compute entry.2.1 (entry.1.read application.input))]
  · simp only [PMF.pure_apply_self, ENNReal.toReal_one, one_smul]
  · intro other _ different
    simp only [PMF.pure_apply, different, if_false, ENNReal.toReal_zero, zero_smul, ite_self]
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

end

end QuantumAlg.Execution
