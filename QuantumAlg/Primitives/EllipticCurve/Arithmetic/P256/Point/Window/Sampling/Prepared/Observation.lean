/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Observation
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Prepared
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Prepared.Observation

/-!
# Store observations of the original literal measured-window sampler

The whole-program equality transports a scalar observation of the real
sampling sequence. Its prepared interpretation retains all original first
and last measurement records; the real native and identity Paths are
inserted by the accepted generic execution law. The observer alone ignores
mathematical histories. No physical record or circuit instruction changes,
and no uniform-source or Born assertion is assumed here.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

namespace Parameters

/-- The same original measured sequence has precisely the compressed interpreter's Store weight. -/
lemma sampling_sequence_storeWeight (parameters : Parameters ctx) (indices : List WindowIndex)
    (Reference : Register)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Fintype History]
    (state : State ctx (SourceRegister.prod Reference) (services.HiddenState × History))
    (effects : Store ctx → Effect (ctx.register.prod (SourceRegister.prod Reference))) :
    Execution.storeEffectWeight (parameters.sequence indices) environment state effects =
      (PreparedStage.run environment
        (parameters.preparedStages indices Reference) state).effectWeight
          (fun record => effects record.1) := by
  have same := congrArg
    (fun code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
        ctx ctx true => Execution.storeEffectWeight code environment state effects)
    (parameters.preparedStages_sequence (services := services) indices Reference)
  exact same.symm.trans
    (PreparedStage.window_preparedSequence_storeWeight environment
      (parameters.preparedStages indices Reference) state effects)

end Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
