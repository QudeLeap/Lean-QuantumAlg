/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Quadratic
import all QuantumAlg.Core.Execution.Instrument.Recorded

/-!
# Arbitrary effects of one complete actual recorded instrument

The same actual pullback is the sum of the final effect's quadratic forms
on every retained outcome vector. The complete returned Store, hidden
service state and actual Path determine that effect. Raw input vectors
keep their original mass; no intermediate norm bound or normalization is
required. A Unit factor below only reindexes a mathematical finite sum.
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

private lemma recorded_quadratic_pure (actual : RecordedInstrument code Outcome environment)
    (Reference : Register) {History : Type} [Finite History]
    (original : Store ctx × (services.HiddenState × History))
    (effects : Circuit.EffectFamily ctx Reference
      (services.HiddenState × (History × code.Path)))
    (vector : NormalizedVector (ctx.register.prod Reference)) :
    HilbertOperator.quadraticWeight
        (code.effectPullback environment Reference effects original).matrix vector =
      ∑ outcome : Outcome,
        HilbertOperator.quadraticWeight
          (effects (sourceFullRetainedRecord (ctx := ctx) (services := services)
            actual.record original outcome)).matrix
          ((referenceLift Reference
            (actual.operator (original.1, original.2.1) outcome)).applyVec vector) := by
  let _ : Fintype History := Fintype.ofFinite History
  have paired := retained_quadratic_pure_two
    (Original := Store ctx × (services.HiddenState × History))
    (First := Unit) (Last := Outcome)
    (Result := Store ctx × (services.HiddenState × (History × code.Path)))
    (R := ctx.register.prod Reference) (Classical.decEq _)
    (fun state => code.execute environment Reference state)
    (fun incoming (_ : Unit) outcome =>
      sourceFullRetainedRecord (ctx := ctx) (services := services) actual.record
        incoming outcome)
    (fun incoming (_ : Unit) outcome => referenceLift Reference
      (actual.operator (incoming.1, incoming.2.1) outcome))
    effects (code.effectPullback environment Reference effects)
    (by
      intro state result
      simp only [Fintype.sum_unique]
      exact (actual.blocks Reference state result).trans (sum_condition_decisions _ _ _ _))
    (fun state => code.effectWeight_execute environment Reference state effects)
    original vector
  simpa only [Fintype.sum_unique] using paired

/-- The same actual pullback retains every outcome with its original raw vector mass. -/
lemma recorded_quadratic (actual : RecordedInstrument code Outcome environment)
    (Reference : Register) {History : Type} [Finite History]
    (original : Store ctx × (services.HiddenState × History))
    (effects : Circuit.EffectFamily ctx Reference
      (services.HiddenState × (History × code.Path)))
    (vector : HilbertVector (ctx.register.prod Reference)) :
    HilbertOperator.quadraticWeight
        (code.effectPullback environment Reference effects original).matrix vector =
      ∑ outcome : Outcome,
        HilbertOperator.quadraticWeight
          (effects (sourceFullRetainedRecord (ctx := ctx) (services := services)
            actual.record original outcome)).matrix
          ((referenceLift Reference
            (actual.operator (original.1, original.2.1) outcome)).applyVec vector) := by
  exact quadratic_sum_of_normalized
    (code.effectPullback environment Reference effects original).matrix
    (fun outcome => (effects (sourceFullRetainedRecord (ctx := ctx) (services := services)
      actual.record original outcome)).matrix)
    (fun outcome => referenceLift Reference
      (actual.operator (original.1, original.2.1) outcome))
    (recorded_quadratic_pure actual Reference original effects) vector

end

end QuantumAlg.Execution.RecordedInstrument
