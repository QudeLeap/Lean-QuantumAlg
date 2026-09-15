/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Seed
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Calibration
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Probability.FailureBudget

/-!
# The original P-256 finite repetition condition

The actual prepared exceptional mass of the one fixed public seed is at most
its original averaging bound. Monotonicity transfers the complete failure
coefficient to the calibrated 4714-repetition bound, including the original
four-square-root error. The certified public instance supplies every premise.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured

noncomputable section

open PrimeFieldShortWeierstrass FiniteCyclicDLP

/-- The actual fixed P-256 seed satisfies the complete original one-percent retry condition. -/
theorem repetitionCondition (I : DomainParameters.PublicKeyInstance) :
    LogicalResources.RepetitionCondition (DomainParameters.curve I.curveCert)
      (Cascade.ecdlpInstance I) (Cascade.addend I) (fixedSeed I) 4714 ((1 : ℝ) / 100) := by
  let problem := ECDLP.Canonical.problem (Cascade.ecdlpInstance I)
  have errorBound :
      4 * Real.sqrt (ECDLP.Measured.preparedExceptionalMass problem
        (Cascade.addend I) (fixedSeed I)) ≤
      4 * Real.sqrt ((2 * (2 * orderWidth problem) : Nat) /
        ((problem.order - 1 : Nat) : ℝ)) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (fixedSeed_exceptionalMass_le I)) (by norm_num)
  have ratioBound :
      1 - ((problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) -
          4 * Real.sqrt (ECDLP.Measured.preparedExceptionalMass problem
            (Cascade.addend I) (fixedSeed I))) ≤
      1 - ((problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) -
          4 * Real.sqrt ((2 * (2 * orderWidth problem) : Nat) /
            ((problem.order - 1 : Nat) : ℝ))) :=
    sub_le_sub_left (sub_le_sub_left errorBound _) _
  have powers := pow_le_pow_left₀
    (ECDLP.Measured.samplingFailureRatio_nonneg problem (Cascade.addend I) (fixedSeed I))
    ratioBound 4714
  exact powers.trans (originalOffsetFailurePower_le_onePercent I)

end

end QuantumAlg.EllipticCurve.P256.Measured
