/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Basic
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Resources
import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Resources
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Finite resource bounds behind the source's amplitude-estimation scaling

The exact elementary ledger has a linear source-width contribution per
iterate and a quadratic phase-readout contribution. The actual selected
binary power is bounded by the inverse precision-confidence product.
These finite inequalities support the source's stated resource scaling
without changing the original selected width or adding resource inputs.
-/

namespace QuantumAlg.AmplitudeEstimation.Elementary

noncomputable section

/-- The actual independent elementary count has the source's linear-plus-quadratic form. -/
theorem unitaryGateCount_le (t n : Nat) :
    unitaryGateCount t n ≤ 13 * n * (2 ^ t - 1) + 5 * t + 5 * t ^ 2 := by
  have reflected : ZeroReflection.controlledElementaryGateCount n ≤ 13 * n := by
    cases n with
    | zero => decide
    | succ n =>
        have bounded := ZeroReflection.controlledElementaryGateCount_le (n + 1)
        omega
  have reflections := Nat.mul_le_mul_left (2 ^ t - 1) reflected
  have phases : t.choose 2 ≤ t * t := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left t (Nat.sub_le t 1))
  have swaps := Nat.div_le_self t 2
  unfold unitaryGateCount
  nlinarith

/-- The original selected phase width uses fewer than four pi over epsilon eta source powers. -/
theorem selected_power_lt {eps η : Real}
    (positivePrecision : 0 < eps) (precisionAtMostOne : eps ≤ 1)
    (positiveFailure : 0 < η) (failureAtMostOne : η ≤ 1) :
    (2 : Real) ^ selectedPhaseQubits eps η < 4 * Real.pi / (eps * η) := by
  let scale : Real := η⁻¹ / precisionRadius eps
  let rounded : Nat := Nat.ceil scale
  have radiusPositive := precisionRadius_pos positivePrecision
  have radiusSmall : precisionRadius eps < 1 := by
    rw [precisionRadius]
    apply (div_lt_one Real.pi_pos).2
    linarith [Real.pi_gt_three]
  have inverseLarge : (1 : Real) ≤ η⁻¹ := by
    simpa using (inv_le_inv₀ (by norm_num : (0 : Real) < 1) positiveFailure).2
      failureAtMostOne
  have scaleLarge : 1 < scale := by
    apply (one_lt_div radiusPositive).2
    exact radiusSmall.trans_le inverseLarge
  have roundedLarge : 1 < rounded := by
    have roundedBound : scale ≤ (rounded : Real) := Nat.le_ceil scale
    by_contra small
    have smallReal : (rounded : Real) ≤ 1 := by exact_mod_cast (by omega : rounded ≤ 1)
    linarith
  have positive : 0 < Nat.clog 2 rounded := Nat.clog_pos (by decide) roundedLarge
  have previous := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) roundedLarge
  have power : 2 ^ Nat.clog 2 rounded < 2 * rounded := by
    calc
      _ = 2 ^ ((Nat.clog 2 rounded).pred + 1) :=
        congrArg (fun exponent : Nat => 2 ^ exponent) (Nat.succ_pred_eq_of_pos positive).symm
      _ = 2 ^ (Nat.clog 2 rounded).pred * 2 := pow_succ _ _
      _ < rounded * 2 := Nat.mul_lt_mul_of_pos_right previous (by decide)
      _ = _ := Nat.mul_comm _ _
  have powerReal : (2 : Real) ^ Nat.clog 2 rounded < 2 * (rounded : Real) := by
    exact_mod_cast power
  have roundedReal : (rounded : Real) < scale + 1 :=
    Nat.ceil_lt_add_one (le_of_lt (lt_trans zero_lt_one scaleLarge))
  calc
    (2 : Real) ^ selectedPhaseQubits eps η < 2 * (scale + 1) :=
      powerReal.trans (mul_lt_mul_of_pos_left roundedReal (by norm_num))
    _ ≤ 4 * scale := by linarith
    _ = _ := by
      dsimp only [scale, precisionRadius]
      field_simp [positivePrecision.ne', positiveFailure.ne', Real.pi_ne_zero]

end

end QuantumAlg.AmplitudeEstimation.Elementary
