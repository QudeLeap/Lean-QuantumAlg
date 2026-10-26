/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Observation
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Prepared.Execution
import all QuantumAlg.Core.Execution.Circuit.Effect

/-!
# Final-Store observations of the same actual prepared execution

The scalar observer is literally the actual circuit's execution followed
by its Store-indexed effect weight. Its return type contains no dependent
Path, so an equality of actual programs transports the observation without
reconstructing their complete record carriers. The execution itself keeps
all original Store, service state, history and actual measurement Paths.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {Reference : Register}

namespace PreparedStage

/-- Adding the real native and identity Paths leaves every final-Store observation unchanged. -/
lemma window_preparedSequence_storeWeight
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (prepared : List (PreparedStage ctx operations services Reference))
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (effects : Store ctx → Effect (ctx.register.prod Reference)) :
    Execution.storeEffectWeight (sequence prepared) environment state effects =
      (run environment prepared state).effectWeight (fun record => effects record.1) := by
  unfold Execution.storeEffectWeight
  rw [window_preparedSequence_execute, State.effectWeight_mapHistory]

end PreparedStage

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
