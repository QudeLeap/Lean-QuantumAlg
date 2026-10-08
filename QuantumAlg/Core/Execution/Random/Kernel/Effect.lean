/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Effect.Weighted
import all QuantumAlg.Core.Execution.Random.Kernel
import all QuantumAlg.Core.Execution.Measurement.Effect
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Exact observations of finite stochastic execution

Each input record pulls its outcome-dependent observable back with its own
declared probabilities. The record can include a persistent service state,
and no independence from that state or the external reference is assumed.
The observable does not introduce an alternative execution channel.
-/

namespace QuantumAlg.Execution

noncomputable section

/-- A declared finite distribution determines its certified backward observable. -/
def kernelEffect {Outcome : Type} [Fintype Outcome] {R : Register}
    (distribution : PMF Outcome) (effects : Outcome → Effect R) : Effect R :=
  Effect.weightedAverage (fun outcome => (distribution outcome).toReal)
    (fun _ => ENNReal.toReal_nonneg) (finite_probability_sum distribution) effects

/-- The backward observable has exactly the actual finite probability weights. -/
theorem kernelEffect_weight {Outcome : Type} [Fintype Outcome] {R : Register}
    (distribution : PMF Outcome) (effects : Outcome → Effect R) (state : DensityOperator R) :
    (kernelEffect distribution effects).weight state =
      ∑ outcome, (distribution outcome).toReal * (effects outcome).weight state :=
  Effect.weightedAverage_weight _ _ _ effects state

end

end QuantumAlg.Execution

namespace QuantumAlg.ExecutionState

noncomputable section

/-- Observing the actual stochastic output equals its record-dependent probability pullback. -/
theorem effectWeight_kernelChoice {C Outcome : Type}
    [Fintype C] [Fintype Outcome] {R : Register} (state : ExecutionState C R)
    (transition : C → PMF Outcome) (effects : C × Outcome → Effect R) :
    (Execution.kernelChoice state transition).effectWeight effects =
      state.effectWeight (fun original => Execution.kernelEffect (transition original)
        (fun outcome => effects (original, outcome))) := by
  simp only [effectWeight, Fintype.sum_prod_type, Execution.kernelEffect_weight]
  simp only [Effect.weight, Execution.kernelChoice_block_matrix, Matrix.mul_smul,
    Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

end

end QuantumAlg.ExecutionState
