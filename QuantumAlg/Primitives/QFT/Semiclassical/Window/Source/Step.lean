/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.State

/-!
# Actual preparation reset before a mathematical source feed

The first and last operations are their actual Circuit interpreters. The
feed between them acts only in the mathematical source observation space.
Their pullback is intrinsically a positive contraction on all source labels,
without an arithmetic-correctness premise. Every original Store, service
state, both real Paths and external reference is retained.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {firstAllocation lastAllocation : Bool}

/-- Actual reset pullback around feed and actual measured-middle pullback. -/
def stepObservable (Reference : Register)
    (feed : UnitaryOperator (ctx.register.prod Reference))
    (first : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx firstAllocation)
    (last : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx lastAllocation)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {History : Type}
    (effects : Circuit.EffectFamily ctx Reference
      (services.HiddenState × ((History × first.Path) × last.Path))) :
    Circuit.EffectFamily ctx Reference (services.HiddenState × History) :=
  first.effectPullback environment Reference
    (observable Reference feed last environment effects)

/-- Exact full-record weight of the same actual reset and middle, with feed between them. -/
lemma window_sourceStep_state_weight (Reference : Register)
    (feed : UnitaryOperator (ctx.register.prod Reference))
    (first : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx firstAllocation)
    (last : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx lastAllocation)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {History : Type} [Fintype History]
    (effects : Circuit.EffectFamily ctx Reference
      (services.HiddenState × ((History × first.Path) × last.Path)))
    (state : State ctx Reference (services.HiddenState × History)) :
    (last.execute environment Reference
      ((first.execute environment Reference state).applyUnitary (fun _ => feed))).effectWeight
        effects =
      state.effectWeight (stepObservable Reference feed first last environment effects) :=
  (window_sourceObservation_state_weight Reference feed last environment effects
    (first.execute environment Reference state)).trans
      (Circuit.effectWeight_execute first environment Reference state
        (observable Reference feed last environment effects))

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
