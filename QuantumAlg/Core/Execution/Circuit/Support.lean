/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit.Effect
import all QuantumAlg.Core.Base.Gate.Effect.Support

/-!
# Coherent support comparison for actual finite circuits

The compared quantities are observations of the existing circuit interpreter,
including arbitrary output stores and histories. Agreement on the complete
coherent good input transfers to the normalized input with four times the
omitted vector norm. Intermediate measurements need not have a unique outcome.
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace ExecutionState

/-- A definite input observes its own effect regardless of the equality decision procedure. -/
theorem effectWeight_ofValue_decision {C : Type} [Fintype C] {R : Register}
    (decision : DecidableEq C) (value : C) (state : DensityOperator R)
    (effects : C → Effect R) :
    (@ofValue C _ R decision value state).effectWeight effects =
      (effects value).weight state := by
  rw [Subsingleton.elim decision (Classical.decEq C)]
  exact effectWeight_ofValue value state effects

/-- An observation independent of the classical record depends only on the full quantum marginal. -/
theorem effectWeight_constant {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (effect : Effect R) :
    state.effectWeight (fun _ => effect) = effect.weight state.quantumMarginal := by
  unfold effectWeight Effect.weight
  change (∑ value, (effect.matrix * (state.block value).matrix).trace.re) =
    (effect.matrix * ∑ value, (state.block value).matrix).trace.re
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

end ExecutionState

namespace Circuit

open Execution

/-- Coherent good-input agreement gives the same error constant for actual measured circuits. -/
theorem effectWeight_execute_le_add_four_mul_omitted_norm
    {model : ExecutionModel} {pre actualPost idealPost : RuntimeCtx model.kind}
    (actual : Circuit model pre actualPost) (ideal : Circuit model pre idealPost)
    (Reference : Register)
    (store : Store pre) (hidden : model.HiddenState)
    (input : NormalizedVector (Register.prod pre.register Reference))
    (good : HilbertVector (Register.prod pre.register Reference)) (bounded : ‖good‖ ≤ 1)
    (actualEffects : EffectFamily actualPost Reference (model.HiddenState × (Unit × actual.Path)))
    (idealEffects : EffectFamily idealPost Reference (model.HiddenState × (Unit × ideal.Path)))
    (agrees :
      (actual.execute Reference (ExecutionState.ofValue (store, (hidden, ()))
        (DensityOperator.ofSubnormalizedVector good bounded))).effectWeight actualEffects =
      (ideal.execute Reference (ExecutionState.ofValue (store, (hidden, ()))
        (DensityOperator.ofSubnormalizedVector good bounded))).effectWeight idealEffects) :
    (ideal.execute Reference (ExecutionState.ofValue (store, (hidden, ()))
      (DensityOperator.ofPure input))).effectWeight idealEffects ≤
      (actual.execute Reference (ExecutionState.ofValue (store, (hidden, ()))
        (DensityOperator.ofPure input))).effectWeight actualEffects +
          4 * ‖(input : HilbertVector (Register.prod pre.register Reference)) - good‖ := by
  simp only [effectWeight_execute, ExecutionState.effectWeight_ofValue_decision] at agrees ⊢
  exact Effect.weight_le_add_four_mul_omitted_norm
    (effectPullback actual Reference actualEffects (store, (hidden, ())))
    (effectPullback ideal Reference idealEffects (store, (hidden, ()))) input good bounded agrees

end Circuit

end

end QuantumAlg
