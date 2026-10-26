/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Observation

/-!
# Source pullback on arbitrary complete actual execution records

This weight identity extends the same positive source observable to an
arbitrary mixture of original Stores, service states and mathematical
histories. The middle is its actual Circuit interpreter, including measured
Paths and allocating classical scopes. No correctness condition on bad
inputs is used. The feed is a mathematical source-coordinate operator only.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel} {allowAllocation : Bool}

/-- Exact actual middle weight after mathematical feed, on every original full-record state. -/
lemma window_sourceObservation_state_weight (Reference : Register)
    (feed : UnitaryOperator (ctx.register.prod Reference))
    (body : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx allowAllocation)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {History : Type} [Fintype History]
    (effects : Circuit.EffectFamily ctx Reference
      (services.HiddenState × (History × body.Path)))
    (state : State ctx Reference (services.HiddenState × History)) :
    (body.execute environment Reference (state.applyUnitary (fun _ => feed))).effectWeight
        effects =
      state.effectWeight (observable Reference feed body environment effects) :=
  (Circuit.effectWeight_execute body environment Reference
    (state.applyUnitary (fun _ => feed)) effects).trans
      (ExecutionState.effectWeight_applyUnitary state (fun _ => feed)
        (body.effectPullback environment Reference effects))

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
