/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Weight
import all QuantumAlg.Core.Execution.Instrument.Recorded

/-!
# The exact total mass of a complete recorded instrument

The actual interpreter preserves the original input mass. Its complete
retained block equation therefore sums the squared norms of all actual
outcome vectors to that same mass. Operators may read the original Store
and hidden service state; returned records may collide. No outcome count,
record injectivity, hidden-state independence or branch normalization is
used. The vector bound only constructs the original subnormalized density.
-/

namespace QuantumAlg.Execution.RecordedInstrument

noncomputable section

open Instrument
open scoped BigOperators

attribute [local instance] Classical.decEq

variable {gates : GateModel} {oracles : OracleModel}
  {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {Outcome : Type} [Fintype Outcome]
  {code : Circuit (.quantum gates oracles operations services) ctx ctx true}
  {environment : (ExecutionModel.quantum gates oracles operations
    services).Environment}

/-- Every actual retained outcome contributes its original, unnormalized vector mass. -/
lemma recorded_sum_norm_sq (actual : RecordedInstrument code Outcome environment)
    (Reference : Register) {History : Type} [Finite History]
    (decision : DecidableEq (Store ctx × (services.HiddenState × History)))
    (original : Store ctx × (services.HiddenState × History))
    (vector : HilbertVector (ctx.register.prod Reference)) (bounded : ‖vector‖ ≤ 1) :
    (∑ outcome : Outcome,
      ‖(referenceLift Reference
        (actual.operator (original.1, original.2.1) outcome)).applyVec vector‖ ^ 2) =
      ‖vector‖ ^ 2 := by
  let _ : Fintype History := Fintype.ofFinite History
  let _ : DecidableEq (Store ctx × (services.HiddenState × History)) := decision
  let initial := @ExecutionState.ofValue (Store ctx × (services.HiddenState × History)) _
    (ctx.register.prod Reference) decision original
    (DensityOperator.ofSubnormalizedVector vector bounded)
  let operator := fun incoming : Store ctx × (services.HiddenState × History) =>
    fun outcome : Outcome => referenceLift Reference
      (actual.operator (incoming.1, incoming.2.1) outcome)
  have fibers : (code.execute environment Reference initial).mass =
      ∑ incoming : Store ctx × (services.HiddenState × History), ∑ outcome : Outcome,
        (operator incoming outcome * (initial.block incoming).matrix *
          (operator incoming outcome).conjTranspose).trace.re := by
    have observed := retained_trace_sum
      (Original := Store ctx × (services.HiddenState × History)) (Outcome := Outcome)
      (Result := Store ctx × (services.HiddenState × (History × code.Path)))
      (R := ctx.register.prod Reference)
      (sourceFullRetainedRecord (ctx := ctx) (services := services) actual.record
        (History := History))
      (fun result => ((code.execute environment Reference initial).block result).matrix)
      (fun incoming outcome => operator incoming outcome * (initial.block incoming).matrix *
        (operator incoming outcome).conjTranspose)
      (by
        intro result
        exact (actual.blocks Reference (History := History) initial result).trans
          (sum_condition_decisions _ _ _ _))
      (fun _ => Effect.one (ctx.register.prod Reference))
    simpa (config := { instances := true }) only [Effect.one, Matrix.one_mul,
      ExecutionState.mass, DensityOperator.mass, ExecutionModel.hiddenStateFintype,
      ExecutionModel.kind, ExecutionModel.HiddenState, ExecutionModel.classicalOracles]
      using observed
  have collapsed :
      (∑ incoming : Store ctx × (services.HiddenState × History), ∑ outcome : Outcome,
        (operator incoming outcome * (initial.block incoming).matrix *
          (operator incoming outcome).conjTranspose).trace.re) =
      ∑ outcome : Outcome, ‖(operator original outcome).applyVec vector‖ ^ 2 := by
    rw [Finset.sum_eq_single original]
    · apply Finset.sum_congr rfl
      intro outcome _
      simp only [initial, ExecutionState.ofValue_block, if_true]
      exact trace_sandwich_vector (operator original outcome) vector bounded
    · intro other _ different
      apply Finset.sum_eq_zero
      intro outcome _
      simp only [initial, ExecutionState.ofValue_block, if_neg different,
        DensityOperator.zero_matrix, Matrix.mul_zero, Matrix.zero_mul, Matrix.trace_zero,
        Complex.zero_re]
    · simp
  calc
    _ = (code.execute environment Reference initial).mass := (fibers.trans collapsed).symm
    _ = initial.mass := code.execute_mass environment Reference initial
    _ = ‖vector‖ ^ 2 := (ExecutionState.ofValue_mass original
      (DensityOperator.ofSubnormalizedVector vector bounded)).trans
        (DensityOperator.ofSubnormalizedVector_mass vector bounded)

end

end QuantumAlg.Execution.RecordedInstrument
