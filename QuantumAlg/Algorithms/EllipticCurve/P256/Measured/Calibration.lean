/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Cascade.Parameters
import all QuantumAlg.Algorithms.FiniteCyclicDLP.PrimeOrderTailBound.P256
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Original P-256 repetition calibration with the complete exceptional error

The original 4714 repetitions leave an analysis reserve of one part in
200000. The original fixed-offset error fits in one equal share of that
reserve per repetition. A pure power perturbation inequality therefore
calibrates the actual complete failure coefficient to one percent, without
using a repeated independent distribution or changing the execution count.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured

noncomputable section

open FiniteCyclicDLP Factoring

private def selectedFloor : ℝ :=
  ((DomainParameters.subgroupOrder * (DomainParameters.subgroupOrder - 1) : Nat) : ℝ) /
    (4 * (PrimeOrderTailBound.P256.fourierModulus : ℝ) ^ 2)

private def exceptionalError : ℝ :=
  4 * Real.sqrt ((1040 : ℝ) / ((DomainParameters.subgroupOrder - 1 : Nat) : ℝ))

private theorem order_le_modulus :
    DomainParameters.subgroupOrder ≤ PrimeOrderTailBound.P256.fourierModulus := by
  rw [PrimeOrderTailBound.P256.fourierModulus_eq]
  norm_num [DomainParameters.subgroupOrder]

private theorem selectedFloor_bounds : (1 : ℝ) / 2048 ≤ selectedFloor ∧ selectedFloor ≤ 1 := by
  rw [selectedFloor, PrimeOrderTailBound.P256.fourierModulus_eq]
  norm_num [DomainParameters.subgroupOrder]

private theorem exceptionalError_le_reserve :
    exceptionalError ≤ (1 : ℝ) / (200000 * 4714) := by
  have certificate : 16 * 1040 * (200000 * 4714) ^ 2 ≤
      DomainParameters.subgroupOrder - 1 := by
    norm_num [DomainParameters.subgroupOrder]
  have certificateReal : ((16 * 1040 * (200000 * 4714) ^ 2 : Nat) : ℝ) ≤
      ((DomainParameters.subgroupOrder - 1 : Nat) : ℝ) := by
    exact_mod_cast certificate
  have denominatorPositive : 0 < ((DomainParameters.subgroupOrder - 1 : Nat) : ℝ) := by
    norm_num [DomainParameters.subgroupOrder]
  have squareBound : (1040 : ℝ) / ((DomainParameters.subgroupOrder - 1 : Nat) : ℝ) ≤
      (1 / (4 * (200000 * 4714 : ℝ))) ^ 2 := by
    rw [show (1 / (4 * (200000 * 4714 : ℝ))) ^ 2 =
      1 / (16 * (200000 * 4714 : ℝ) ^ 2) by ring]
    apply (div_le_div_iff₀ denominatorPositive (by positivity)).2
    norm_num only [one_mul, Nat.cast_mul, Nat.cast_pow] at certificateReal
    nlinarith
  have rootBound : Real.sqrt
      ((1040 : ℝ) / ((DomainParameters.subgroupOrder - 1 : Nat) : ℝ)) ≤
      1 / (4 * (200000 * 4714 : ℝ)) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
    rw [Real.sq_sqrt (by positivity)]
    exact squareBound
  unfold exceptionalError
  calc
    _ ≤ 4 * (1 / (4 * (200000 * 4714 : ℝ))) :=
      mul_le_mul_of_nonneg_left rootBound (by norm_num)
    _ = _ := by norm_num

private theorem idealFailure_eq_source :
    1 - selectedFloor =
      (PrimeOrderTailBound.sourceFailureBudget DomainParameters.subgroupOrder
        PrimeOrderTailBound.P256.fourierModulus).value := by
  have subtraction := (PrimeOrderTailBound.successNumerator_lt_successDenominator
    (by norm_num [DomainParameters.subgroupOrder] : 2 ≤ DomainParameters.subgroupOrder)
    order_le_modulus).le
  unfold selectedFloor PrimeOrderTailBound.sourceFailureBudget FailureBudget.value
  rw [Nat.cast_sub subtraction]
  simp only [PrimeOrderTailBound.successNumerator, PrimeOrderTailBound.successDenominator,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have modulusPositive : 0 < (PrimeOrderTailBound.P256.fourierModulus : ℝ) := by
    rw [PrimeOrderTailBound.P256.fourierModulus_eq]
    positivity
  field_simp

private theorem idealFailure_power_le_analysis :
    (1 - selectedFloor) ^ 4714 ≤ (1999 : ℝ) / 200000 := by
  have calibrated := FailureBudget.retryFailurePowerForReal_le
    (PrimeOrderTailBound.sourceFailureBudget DomainParameters.subgroupOrder
      PrimeOrderTailBound.P256.fourierModulus)
    PrimeOrderTailBound.P256.analysisFailureBudget
    (PrimeOrderTailBound.sourceFailureBudget_strictlyWellFormed
      (by norm_num [DomainParameters.subgroupOrder]) order_le_modulus)
    PrimeOrderTailBound.P256.analysisFailureBudget_wellFormed
  change (PrimeOrderTailBound.sourceFailureBudget DomainParameters.subgroupOrder
      PrimeOrderTailBound.P256.fourierModulus).value ^
        PrimeOrderTailBound.retryCount DomainParameters.subgroupOrder
          PrimeOrderTailBound.P256.fourierModulus PrimeOrderTailBound.P256.analysisFailureBudget ≤
      (1999 : ℝ) / 200000 at calibrated
  rw [PrimeOrderTailBound.P256.analysisRetryCount_eq_4714] at calibrated
  rw [idealFailure_eq_source]
  exact calibrated

private theorem power_perturbation {a b : ℝ} (nonnegative : 0 ≤ b)
    (ordered : b ≤ a) (bounded : a ≤ 1) (count : Nat) :
    a ^ count ≤ b ^ count + count * (a - b) := by
  have aNonnegative := nonnegative.trans ordered
  have absoluteBound : max |a| |b| ≤ 1 := by
    rw [abs_of_nonneg aNonnegative, abs_of_nonneg nonnegative]
    exact max_le bounded (ordered.trans bounded)
  have powersBound : max |a| |b| ^ (count - 1) ≤ 1 :=
    pow_le_one₀ (le_max_of_le_left (abs_nonneg _)) absoluteBound
  have difference := (le_abs_self (a ^ count - b ^ count)).trans
    (abs_pow_sub_pow_le (a := a) (b := b) (n := count))
  have estimate := difference.trans (mul_le_mul_of_nonneg_left powersBound
    (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)))
  rw [mul_one, abs_of_nonneg (sub_nonneg.mpr ordered)] at estimate
  linarith

/-- The original 4714 repetitions cover the complete fixed-offset P-256 error. -/
private theorem correctedFailurePower_le_onePercent :
    (1 - (selectedFloor - exceptionalError)) ^ 4714 ≤ (1 : ℝ) / 100 := by
  have errorNonnegative : 0 ≤ exceptionalError := by
    unfold exceptionalError
    positivity
  have ordered : 1 - selectedFloor ≤ 1 - (selectedFloor - exceptionalError) :=
    sub_le_sub_left (sub_le_self _ errorNonnegative) _
  have errorBelowFloor : exceptionalError ≤ selectedFloor :=
    exceptionalError_le_reserve.trans
      ((by norm_num : (1 : ℝ) / (200000 * 4714) ≤ 1 / 2048).trans selectedFloor_bounds.1)
  have bounded : 1 - (selectedFloor - exceptionalError) ≤ 1 :=
    sub_le_self _ (sub_nonneg.mpr errorBelowFloor)
  have perturbation := power_perturbation (sub_nonneg.mpr selectedFloor_bounds.2)
    ordered bounded 4714
  have accumulated := mul_le_mul_of_nonneg_left exceptionalError_le_reserve
    (by norm_num : (0 : ℝ) ≤ 4714)
  have difference : (1 - (selectedFloor - exceptionalError)) - (1 - selectedFloor) =
      exceptionalError := by ring
  rw [difference] at perturbation
  exact perturbation.trans
    ((add_le_add idealFailure_power_le_analysis accumulated).trans_eq (by norm_num))

/-- The original known-order P-256 expression has a complete one-percent failure budget. -/
theorem originalOffsetFailurePower_le_onePercent (publicKey : DomainParameters.PublicKeyInstance) :
    let problem := PrimeFieldShortWeierstrass.ECDLP.Canonical.problem
      (Cascade.ecdlpInstance publicKey)
    (1 - ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt ((2 * (2 * orderWidth problem) : Nat) /
          ((problem.order - 1 : Nat) : ℝ)))) ^ 4714 ≤ (1 : ℝ) / 100 := by
  dsimp only
  have width := Cascade.exponentWidth_eq_260 publicKey
  change orderWidth (PrimeFieldShortWeierstrass.ECDLP.Canonical.problem
    (Cascade.ecdlpInstance publicKey)) = 260 at width
  have order : (PrimeFieldShortWeierstrass.ECDLP.Canonical.problem
      (Cascade.ecdlpInstance publicKey)).order = DomainParameters.subgroupOrder := rfl
  rw [fourierModulus, width, order, Nat.totient_prime publicKey.subgroupCert.prime]
  change (1 - ((DomainParameters.subgroupOrder : ℝ) *
      (DomainParameters.subgroupOrder - 1 : Nat) /
        (4 * (PrimeOrderTailBound.P256.fourierModulus : ℝ) ^ 2) -
          4 * Real.sqrt ((1040 : ℝ) /
            ((DomainParameters.subgroupOrder - 1 : Nat) : ℝ)))) ^ 4714 ≤ _
  simpa only [selectedFloor, exceptionalError, Nat.cast_mul] using
    correctedFailurePower_le_onePercent

end

end QuantumAlg.EllipticCurve.P256.Measured
