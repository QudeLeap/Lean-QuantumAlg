/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Step
import all QuantumAlg.Core.Execution.Random.Kernel.Effect
import all QuantumAlg.Core.Execution.State.Effect

/-!
# Certified observations of actual classical instructions

Native and oracle observations use their declarations' exact probabilities,
actual caller writes and recorded outputs. Oracle observations additionally
use the returned persistent state, including its correlation with the result.
These equations hold against arbitrary quantum-reference input blocks.
-/

namespace QuantumAlg.Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {H : Type} [Fintype H]

/-- A native step uses the declaration's probability-weighted observable after its real write. -/
lemma effectWeight_nativeStep {operations : ClassicalOpModel}
    (application : operations.Application ctx) (state : State ctx Reference H)
    (effects : Store ctx × (H × (operations.outputShape application.token).Value) →
      Effect (ctx.register.prod Reference)) :
    (nativeStep application state).effectWeight effects =
      state.effectWeight (fun original => kernelEffect
        (operations.evaluate application.token (original.1.read application.input))
        (fun result => effects
          (original.1.write application.output result, (original.2, result)))) := by
  dsimp only [nativeStep]
  rw [ExecutionState.effectWeight_mapClassical_decision, ExecutionState.effectWeight_kernelChoice]

/-- A query observation retains the actual joint next-service-state and visible-result weights. -/
lemma effectWeight_queryStep {oracles : ClassicalOracleModel}
    (application : oracles.Application ctx) (environment : oracles.Interpretation)
    (state : State ctx Reference (oracles.HiddenState × H))
    (effects : Store ctx × (oracles.HiddenState ×
      (H × (oracles.outputShape application.query).Value)) → Effect (ctx.register.prod Reference)) :
    (queryStep environment application state).effectWeight effects =
      state.effectWeight (fun original => kernelEffect
        (oracles.transition environment application.query original.2.1
          (original.1.read application.input))
        (fun result => effects (original.1.write application.output result.2,
          (result.1, (original.2.2, result.2))))) := by
  dsimp only [queryStep]
  rw [ExecutionState.effectWeight_mapClassical_decision, ExecutionState.effectWeight_kernelChoice]

end

end QuantumAlg.Execution
