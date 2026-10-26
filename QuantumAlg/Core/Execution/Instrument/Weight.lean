/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Core.Execution.Instrument.Observation
import all QuantumAlg.Core.Base.State.Density.Vector

/-!
# Event weights of every actual retained Kraus fiber

The complete interpreter block equation gives the exact final event sum.
Every original Store, hidden state, history and actual Path is retained;
colliding record writes add their separate density contributions. No
outcome-to-record injectivity, unitary operator or normalized branch is
assumed. An unnormalized coherent input keeps its original squared norm.
-/

namespace QuantumAlg.Execution

noncomputable section

open Instrument
open scoped BigOperators

attribute [local instance] Classical.decEq

private lemma retained_trace_sum {Original Outcome Result : Type}
    [Fintype Original] [Fintype Outcome] [Fintype Result] [DecidableEq Result]
    {R : Register} (record : Original → Outcome → Result)
    (blocks : Result → HilbertOperator R) (parts : Original → Outcome → HilbertOperator R)
    (actual : ∀ result, blocks result = ∑ original, ∑ outcome,
      if record original outcome = result then parts original outcome else 0)
    (effects : Result → Effect R) :
    (∑ result, ((effects result).matrix * blocks result).trace.re) =
      ∑ original, ∑ outcome,
        ((effects (record original outcome)).matrix * parts original outcome).trace.re := by
  have expanded (result : Result) :
      ((effects result).matrix * blocks result).trace.re =
        ∑ original, ∑ outcome, if record original outcome = result then
          ((effects result).matrix * parts original outcome).trace.re else 0 := by
    rw [actual]
    simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro original _
    apply Finset.sum_congr rfl
    intro outcome _
    by_cases selected : record original outcome = result
    · rw [if_pos selected, if_pos selected]
    · simp only [if_neg selected, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]
  simp_rw [expanded]
  calc
    _ = ∑ original, ∑ result, ∑ outcome, if record original outcome = result then
        ((effects result).matrix * parts original outcome).trace.re else 0 :=
      Finset.sum_comm
    _ = ∑ original, ∑ outcome, ∑ result, if record original outcome = result then
        ((effects result).matrix * parts original outcome).trace.re else 0 := by
      apply Finset.sum_congr rfl
      intro original _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro original _
      apply Finset.sum_congr rfl
      intro outcome _
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

private lemma trace_sandwich_vector {R : Register} (operator : HilbertOperator R)
    (vector : HilbertVector R) (bounded : ‖vector‖ ≤ 1) :
    (operator * (DensityOperator.ofSubnormalizedVector vector bounded).matrix *
      operator.conjTranspose).trace.re = ‖operator.applyVec vector‖ ^ 2 := by
  let values : R.Index → Complex := fun index => vector index
  change (operator * Matrix.vecMulVec values (star values) * operator.conjTranspose).trace.re = _
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec operator values]
  exact DensityOperator.trace_vectorOuterProduct (operator.applyVec vector)

namespace Instrument

variable {gates : GateModel} {oracles : OracleModel}
  {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {allowAllocation : Bool} {Outcome : Type} [Fintype Outcome]
  {code : Circuit (.quantum gates oracles operations services)
    ctx ctx allowAllocation}
  {environment : (ExecutionModel.quantum gates oracles operations
    services).Environment}

/-- Every complete actual record contributes its original operator sandwich exactly once. -/
lemma instrument_effectWeight_eq_retained_sum (actual : Instrument code Outcome environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (effects : Circuit.EffectFamily ctx Reference
      (services.HiddenState × (History × code.Path))) :
    (code.execute environment Reference state).effectWeight effects =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Outcome,
        ((effects (retainedRecord (services := services) actual.record original outcome)).matrix *
          (referenceLift Reference (actual.operator original.1 outcome) *
            (state.block original).matrix *
            (referenceLift Reference (actual.operator original.1 outcome)).conjTranspose)
          ).trace.re := by
  unfold ExecutionState.effectWeight Effect.weight
  apply retained_trace_sum (retainedRecord (services := services) actual.record)
    (fun result => ((code.execute environment Reference state).block result).matrix)
    (fun original outcome => referenceLift Reference (actual.operator original.1 outcome) *
      (state.block original).matrix *
        (referenceLift Reference (actual.operator original.1 outcome)).conjTranspose)
    _ effects
  intro result
  exact (actual.blocks Reference state result).trans (sum_condition_decisions _ _ _ _)

/-- A Store event weights all actual Kraus fibers, even when their returned records collide. -/
lemma instrument_storeEvent_weight
    {code : Circuit (.quantum gates oracles operations services) ctx ctx true}
    (actual : Instrument code Outcome environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (event : Store ctx → Bool) :
    storeEffectWeight code environment state
        (recordEventEffect (ctx.register.prod Reference) event) =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Outcome,
        if event (actual.record original.1 outcome).1 = true then
          (referenceLift Reference (actual.operator original.1 outcome) *
            (state.block original).matrix *
            (referenceLift Reference (actual.operator original.1 outcome)).conjTranspose
          ).trace.re else 0 := by
  have observed := actual.instrument_effectWeight_eq_retained_sum Reference state
    (fun record => recordEventEffect (ctx.register.prod Reference) event record.1)
  refine observed.trans ?_
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  change ((recordEventEffect (ctx.register.prod Reference) event
      (actual.record original.1 outcome).1).matrix *
      (referenceLift Reference (actual.operator original.1 outcome) *
        (state.block original).matrix *
        (referenceLift Reference (actual.operator original.1 outcome)).conjTranspose)).trace.re = _
  unfold recordEventEffect
  by_cases selected : event (actual.record original.1 outcome).1 = true
  · rw [if_pos selected, if_pos selected]
    change ((1 : HilbertOperator (ctx.register.prod Reference)) * _).trace.re = _
    rw [Matrix.one_mul]
  · rw [if_neg selected, if_neg selected]
    change ((0 : HilbertOperator (ctx.register.prod Reference)) * _).trace.re = _
    rw [Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re]

/-- The original subnormalized input gives the sum of the actual outcome-vector masses. -/
lemma instrument_storeEvent_subnormalized
    {code : Circuit (.quantum gates oracles operations services) ctx ctx true}
    (actual : Instrument code Outcome environment) (Reference : Register)
    {History : Type} [Fintype History]
    (decision : DecidableEq (Store ctx × (services.HiddenState × History)))
    (original : Store ctx × (services.HiddenState × History))
    (vector : HilbertVector (ctx.register.prod Reference)) (bounded : ‖vector‖ ≤ 1)
    (event : Store ctx → Bool) :
    storeEffectWeight code environment
        (@ExecutionState.ofValue (Store ctx × (services.HiddenState × History)) _
          (ctx.register.prod Reference) decision original
          (DensityOperator.ofSubnormalizedVector vector bounded))
        (recordEventEffect (ctx.register.prod Reference) event) =
      ∑ outcome : Outcome, if event (actual.record original.1 outcome).1 = true then
        ‖(referenceLift Reference (actual.operator original.1 outcome)).applyVec vector‖ ^ 2
        else 0 := by
  refine (actual.instrument_storeEvent_weight Reference
    (@ExecutionState.ofValue (Store ctx × (services.HiddenState × History)) _
      (ctx.register.prod Reference) decision original
      (DensityOperator.ofSubnormalizedVector vector bounded)) event).trans ?_
  rw [Finset.sum_eq_single original]
  · apply Finset.sum_congr rfl
    intro outcome _
    by_cases selected : event (actual.record original.1 outcome).1 = true
    · simp only [if_pos selected, ExecutionState.ofValue_block, if_true]
      exact trace_sandwich_vector _ vector bounded
    · simp only [if_neg selected]
  · intro other _ different
    apply Finset.sum_eq_zero
    intro outcome _
    simp only [ExecutionState.ofValue_block, if_neg different, DensityOperator.zero_matrix,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re, ite_self]
  · simp

end Instrument

end

end QuantumAlg.Execution
