/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Completions
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Chronology
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Sequence.Instrument

/-!
# The complete coherent observation of each actual chronological suffix

The suffix starts with both exact rows already retained in its original
Store. Every later reset and measured-middle outcome, hidden service state
and complete Path is retained by the same recursive quadratic observation.
The final event reads the actual two complete physical output streams.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- Observe the same remaining actual instruments on the whole incoming coherent boundary. -/
def suffixValue (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (processed : Nat) (within : processed ≤ 34)
    {Reference : Register} {History : Type}
    (original : Store ctx × (services.HiddenState × History))
    (amplitude : GoodBranch I → ℂ) (reference : HilbertVector Reference)
    (event : Sampling.SourceRegister.Index → Bool) : ℝ :=
  Stage.quadraticSum environment
    (parameters.sourceStages (Sampling.schedule.drop processed) Reference)
    (parameters.sourceCertificates Reference environment (Sampling.schedule.drop processed))
    (fun record => recordEventEffect (ctx.register.prod (Sampling.SourceRegister.prod Reference))
      (fun store => event (storedComplete parameters store)) record.1)
    original
    (coherentPrefix parameters I processed within (consumedCount processed)
      (prefixAmplitude parameters I (firstCount processed) (secondCount processed)
        (firstCount_le processed) (secondCount_le processed within) original.1 amplitude)
      reference)

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
