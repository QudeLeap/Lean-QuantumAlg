/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.Factoring.Common
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Prime-order selected-tail amplification

This module isolates the width-independent probability floor and retry
calibration used by finite-cyclic and elliptic-curve discrete logarithms.
-/

section

namespace QuantumAlg

open Factoring

noncomputable section

namespace FiniteCyclicDLP
namespace PrimeOrderTailBound

/-- Numerator `r(r-1)` of the prime-order selected-tail success floor. -/
def successNumerator (r : Nat) : Nat :=
  r * (r - 1)

/-- Denominator `4q^2` of the prime-order selected-tail success floor. -/
def successDenominator (q : Nat) : Nat :=
  4 * q ^ 2

/-- Exact one-attempt failure complement forced by the prime-order tail bound. -/
def sourceFailureBudget (r q : Nat) : FailureBudget where
  failureNumerator := successDenominator q - successNumerator r
  failureDenominator := successDenominator q

/-- Retry count obtained from the prime-order tail bound and a rational target
failure parameter `eta`. -/
def retryCount (r q : Nat) (η : FailureBudget) : Nat :=
  FailureBudget.retryCountFor (sourceFailureBudget r q) η

theorem successNumerator_pos {r : Nat} (hr : 2 ≤ r) :
    0 < successNumerator r := by
  unfold successNumerator
  exact Nat.mul_pos (by omega) (by omega)

theorem successNumerator_lt_successDenominator {r q : Nat}
    (hr : 2 ≤ r) (hrq : r ≤ q) :
    successNumerator r < successDenominator q := by
  have hq : 0 < q := lt_of_lt_of_le (by omega : 0 < r) hrq
  have hpred : r - 1 < r := by omega
  have hrr : r * (r - 1) < r * r :=
    (Nat.mul_lt_mul_left (by omega : 0 < r)).2 hpred
  have hrqSq : r * r ≤ q * q := Nat.mul_le_mul hrq hrq
  unfold successNumerator successDenominator
  nlinarith

/-- For `2 ≤ r ≤ q`, the rational one-attempt failure complement lies
strictly between zero and one. -/
theorem sourceFailureBudget_strictlyWellFormed {r q : Nat}
    (hr : 2 ≤ r) (hrq : r ≤ q) :
    (sourceFailureBudget r q).StrictlyWellFormed := by
  have hsuccess : 0 < successNumerator r := successNumerator_pos hr
  have hlt : successNumerator r < successDenominator q :=
    successNumerator_lt_successDenominator hr hrq
  refine
    { toWellFormed :=
        { numerator_pos := ?_
          denominator_pos := ?_
          numerator_le_denominator := ?_ }
      numerator_lt_denominator := ?_ }
  · simpa only [sourceFailureBudget] using Nat.sub_pos_of_lt hlt
  · simpa only [sourceFailureBudget] using lt_trans hsuccess hlt
  · simp only [sourceFailureBudget]
    omega
  · simp only [sourceFailureBudget]
    omega

/-- The shared `r,q,eta` retry calibration is the literal closed form
`max{1, ceil(log(1/eta) / log(4q²/(4q²-r(r-1))))}`. -/
theorem retryCount_eq_closedForm (r q : Nat) (η : FailureBudget) :
    retryCount r q η =
      max 1 (Nat.ceil
        (Real.log
            ((η.failureDenominator : Real) /
              η.failureNumerator) /
          Real.log
            (((4 * q ^ 2 : Nat) : Real) /
              ((4 * q ^ 2 - r * (r - 1) : Nat) : Real)))) := by
  unfold retryCount FailureBudget.retryCountFor
    FailureBudget.retryExponentFor sourceFailureBudget
    successDenominator successNumerator
  rfl

/-- The parameterized closed-form count reduces the geometric failure bound
below every well-formed rational target `eta`. -/
theorem retryFailurePower_le {r q : Nat} (η : FailureBudget)
    (hr : 2 ≤ r) (hrq : r ≤ q) (heta : η.WellFormed) :
    (ENNReal.ofReal (sourceFailureBudget r q).value) ^
        retryCount r q η ≤ ENNReal.ofReal η.value := by
  simpa [retryCount] using
    FailureBudget.retryFailurePowerFor_le
      (sourceFailureBudget r q) η
      (sourceFailureBudget_strictlyWellFormed hr hrq) heta

/-- A quadratic Taylor certificate for small positive logarithms. It is kept
generic so endpoint instantiations reduce the remaining inequalities to exact
rational arithmetic. -/
theorem abs_log_one_add_sub_quadratic_le {x : Real}
    (hx : 0 ≤ x) (hxlt : x < 1) :
    |Real.log (1 + x) - (x - x ^ 2 / 2)| ≤
      x ^ 3 / (3 * (1 - x)) := by
  have hcomplex := Complex.norm_log_sub_logTaylor_le 2
    (z := (x : Complex)) (by simpa [abs_of_nonneg hx] using hxlt)
  have hpolynomial :
      Complex.logTaylor 3 (x : Complex) =
        ((x - x ^ 2 / 2 : Real) : Complex) := by
    norm_num [Complex.logTaylor, Finset.sum_range_succ]
    ring
  have hlog :
      Complex.log (1 + (x : Complex)) =
        (Real.log (1 + x) : Complex) := by
    simpa using
      (Complex.ofReal_log (by positivity : 0 ≤ 1 + x)).symm
  rw [hpolynomial, hlog] at hcomplex
  rw [← Complex.ofReal_sub] at hcomplex
  rw [Complex.norm_real] at hcomplex
  norm_num [abs_of_nonneg hx, div_eq_mul_inv] at hcomplex
  have hreal :
      |Real.log (1 + x) - (x - x ^ 2 / 2)| ≤
        x ^ 3 * (1 - x)⁻¹ / 3 := by
    simpa [div_eq_mul_inv] using hcomplex
  calc
    |Real.log (1 + x) - (x - x ^ 2 / 2)| ≤
        x ^ 3 * (1 - x)⁻¹ / 3 := hreal
    _ = x ^ 3 / (3 * (1 - x)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- A pair of certified logarithmic comparisons determines the exact positive
integer selected by the shared ceiling formula. -/
theorem retryCount_eq_of_log_bounds {r q count : Nat}
    (η : FailureBudget) (hcount : 1 ≤ count)
    (hsourceLog :
      0 < Real.log
        (((4 * q ^ 2 : Nat) : Real) /
          ((4 * q ^ 2 - r * (r - 1) : Nat) : Real)))
    (hlower :
      ((count - 1 : Nat) : Real) *
          Real.log
            (((4 * q ^ 2 : Nat) : Real) /
              ((4 * q ^ 2 - r * (r - 1) : Nat) : Real)) <
        Real.log
          ((η.failureDenominator : Real) /
            η.failureNumerator))
    (hupper :
      Real.log
          ((η.failureDenominator : Real) /
            η.failureNumerator) ≤
        (count : Real) *
          Real.log
            (((4 * q ^ 2 : Nat) : Real) /
              ((4 * q ^ 2 - r * (r - 1) : Nat) : Real))) :
    retryCount r q η = count := by
  rw [retryCount_eq_closedForm]
  let exponent :=
    Real.log
        ((η.failureDenominator : Real) /
          η.failureNumerator) /
      Real.log
        (((4 * q ^ 2 : Nat) : Real) /
          ((4 * q ^ 2 - r * (r - 1) : Nat) : Real))
  have hexponentLower : ((count - 1 : Nat) : Real) < exponent := by
    exact (lt_div_iff₀ hsourceLog).2 hlower
  have hexponentUpper : exponent ≤ (count : Real) := by
    exact (div_le_iff₀ hsourceLog).2 hupper
  have hceilUpper : Nat.ceil exponent ≤ count :=
    Nat.ceil_le.mpr hexponentUpper
  have hceilLower : count ≤ Nat.ceil exponent := by
    have hcast : ((count - 1 : Nat) : Real) < (Nat.ceil exponent : Nat) :=
      hexponentLower.trans_le (Nat.le_ceil exponent)
    have hnat : count - 1 < Nat.ceil exponent := by exact_mod_cast hcast
    omega
  have hceil : Nat.ceil exponent = count :=
    Nat.le_antisymm hceilUpper hceilLower
  change max 1 (Nat.ceil exponent) = count
  rw [hceil, max_eq_right hcount]

end PrimeOrderTailBound
end FiniteCyclicDLP

end

end QuantumAlg

end
