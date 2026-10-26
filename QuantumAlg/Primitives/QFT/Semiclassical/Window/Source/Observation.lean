/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Feed
import all QuantumAlg.Core.Execution.Circuit.Support

/-!
# Source observations pulled through the same actual measured circuit

The circuit argument is its real interpreter, including arbitrary allocating
classical scopes, complete Store updates and measured Paths. Its certified
Core pullback is composed only with the mathematical source feed. The result
is intrinsically a positive contraction on every source vector, including bad
branches. No point-correctness or all-label address-preservation premise is
needed for that fact; good-column arithmetic is a separate later theorem.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open Execution

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {ctx : RuntimeCtx .quantum}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel} {allowAllocation : Bool}

/-- Actual interpreter pullback after source feed, retaining all original record arguments. -/
def observable (Reference : Register)
    (feed : UnitaryOperator (ctx.register.prod Reference))
    (body : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx allowAllocation)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {History : Type}
    (effects : Circuit.EffectFamily ctx Reference
      (services.HiddenState × (History × body.Path))) :
    Circuit.EffectFamily ctx Reference
      (services.HiddenState × History) :=
  fun original => Effect.pullbackUnitary feed
    (body.effectPullback environment Reference effects original)

/-- Its exact weight is the same actual execution on the mathematically fed input density. -/
lemma window_sourceObservation_weight (Reference : Register)
    (feed : UnitaryOperator (ctx.register.prod Reference))
    (body : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx allowAllocation)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {History : Type} [Fintype History]
    (effects : Circuit.EffectFamily ctx Reference
      (services.HiddenState × (History × body.Path)))
    (original : Store ctx × (services.HiddenState × History))
    (density : DensityOperator (ctx.register.prod Reference)) :
    (observable Reference feed body environment effects original).weight density =
      (body.execute environment Reference
        (ExecutionState.ofValue original
          (DensityOperator.applyUnitary feed density))).effectWeight
            effects := by
  rw [observable, Effect.weight_pullbackUnitary]
  exact ((Circuit.effectWeight_execute body environment Reference
    (ExecutionState.ofValue original
      (DensityOperator.applyUnitary feed density)) effects).trans
        (ExecutionState.effectWeight_ofValue_decision _ original _ _)).symm

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
