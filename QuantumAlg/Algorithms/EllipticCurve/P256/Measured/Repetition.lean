/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.Resources.Spec
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Seed
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Calibration

/-!
# Fixed-seed calibration for the complete P-256 contract

The original exceptional-mass bound and repetition analysis discharge the
finite-retry condition for the same fixed seed and exactly 4714 attempts.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured

noncomputable section

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP

/-- The existing calibration bounds this fixed seed's complete exceptional-error coefficient. -/
lemma fixedSeed_repetitionCondition (I : P256.DomainParameters.PublicKeyInstance) :
    LogicalResources.RepetitionCondition (P256.DomainParameters.curve I.curveCert)
      (P256.Cascade.ecdlpInstance I) (P256.Cascade.addend I) (P256.Measured.fixedSeed I)
        4714 ((1 : ℝ) / 100) := by
  let problem := ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I)
  have errorBound :
      4 * Real.sqrt (ECDLP.Measured.preparedExceptionalMass problem
        (P256.Cascade.addend I) (P256.Measured.fixedSeed I)) ≤
      4 * Real.sqrt ((2 * (2 * orderWidth problem) : Nat) /
        ((problem.order - 1 : Nat) : ℝ)) :=
    mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (P256.Measured.fixedSeed_exceptionalMass_le I)) (by norm_num)
  have ratioBound :
      1 - ((problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) -
          4 * Real.sqrt (ECDLP.Measured.preparedExceptionalMass problem
            (P256.Cascade.addend I) (P256.Measured.fixedSeed I))) ≤
      1 - ((problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) -
          4 * Real.sqrt ((2 * (2 * orderWidth problem) : Nat) /
            ((problem.order - 1 : Nat) : ℝ))) :=
    sub_le_sub_left (sub_le_sub_left errorBound _) _
  have powers := pow_le_pow_left₀
    (ECDLP.Measured.samplingFailureRatio_nonneg problem
      (P256.Cascade.addend I) (P256.Measured.fixedSeed I)) ratioBound 4714
  exact powers.trans (P256.Measured.originalOffsetFailurePower_le_onePercent I)

end

end QuantumAlg.EllipticCurve.P256.Measured
