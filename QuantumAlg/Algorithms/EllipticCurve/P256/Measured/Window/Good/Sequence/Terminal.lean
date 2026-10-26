/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Sequence.State
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Sequence.Schedule
import all QuantumAlg.Core.Execution.Instrument.Observation.Quadratic

/-!
# The actual empty suffix has its one complete coherent output weight

After all thirty-four windows, both retained prefixes are complete. The
remaining actual observation is the original event on that exact Store,
and the completion sum has precisely its one matching physical tuple.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- The complete retained tuple gives exactly the actual empty-suffix event mass. -/
lemma suffixValue_terminal (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type}
    (original : Store ctx × (services.HiddenState × History))
    (amplitude : GoodBranch I → ℂ) (reference : HilbertVector Reference)
    (event : Sampling.SourceRegister.Index → Bool) :
    suffixValue parameters I environment 34 (Nat.le_refl 34)
        original amplitude reference event =
      completionWeight parameters I 260 260 (Nat.le_refl 260) (Nat.le_refl 260)
        original.1 amplitude reference event := by
  unfold suffixValue
  rw [schedule_drop_final]
  simp only [Sampling.Parameters.sourceStages, Sampling.Parameters.sourceCertificates,
    firstCount_final, secondCount_final, consumedCount_final]
  rw [prefixAmplitude_terminal, completionWeight_terminal]
  exact recordEventEffect_quadratic
    (fun store => event (storedComplete parameters store)) original.1 _

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
