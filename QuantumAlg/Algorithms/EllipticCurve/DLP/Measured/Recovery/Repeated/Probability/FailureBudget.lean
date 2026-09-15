/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Support

/-!
# The original sampling failure ratio is nonnegative

The selected-family floor keeps its original order, totient and Fourier
modulus. Subtracting the original four-square-root exceptional error cannot
increase it. These inequalities do not assert a positive corrected floor or
change the retry domain.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open FiniteCyclicDLP

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original selected floor with its complete exceptional error never exceeds one. -/
theorem samplingCandidateFloor_le_one (problem : KnownOrderProblem (GroupPoint E))
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E) :
    (problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) -
      4 * Real.sqrt (preparedExceptionalMass problem points seed) ≤ 1 := by
  have orderBound : (problem.order : ℝ) ≤ (fourierModulus problem : ℝ) := by
    exact_mod_cast order_le_fourierModulus problem
  have totientBound : (Nat.totient problem.order : ℝ) ≤ (problem.order : ℝ) := by
    exact_mod_cast Nat.totient_le problem.order
  have modulusPositive : 0 < (fourierModulus problem : ℝ) := by
    unfold fourierModulus
    positivity
  have productBound : (problem.order : ℝ) * Nat.totient problem.order ≤
      (fourierModulus problem : ℝ) ^ 2 := by
    calc
      _ ≤ (problem.order : ℝ) * problem.order :=
        mul_le_mul_of_nonneg_left totientBound (Nat.cast_nonneg _)
      _ ≤ (fourierModulus problem : ℝ) * fourierModulus problem :=
        mul_self_le_mul_self (Nat.cast_nonneg _) orderBound
      _ = _ := by ring
  have numeratorBound : (problem.order : ℝ) * Nat.totient problem.order <
      4 * (fourierModulus problem : ℝ) ^ 2 := by
    nlinarith [sq_pos_of_pos modulusPositive]
  have selectedBound : (problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) < 1 :=
    (div_lt_one (by positivity)).mpr numeratorBound
  exact (sub_le_self _ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).trans selectedBound.le

/-- The exact original failure coefficient can multiply inequalities in the actual loop. -/
theorem samplingFailureRatio_nonneg (problem : KnownOrderProblem (GroupPoint E))
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E) :
    0 ≤ 1 - ((problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) -
      4 * Real.sqrt (preparedExceptionalMass problem points seed)) :=
  sub_nonneg.mpr (samplingCandidateFloor_le_one problem points seed)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
