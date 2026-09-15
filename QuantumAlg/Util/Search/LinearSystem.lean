/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.Real.Amplification
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Linear-system analysis parameters

These scalar expressions and rotation bounds do not assert an executed solver cost or success
  probability.
-/

@[expose] public section

namespace QuantumAlg.LinearSystem

/-- The scalar parameter `1/(4κ²)`; no probability lower bound is assumed or derived here. -/
noncomputable def inverseSquareParameter (κ : ℝ) : ℝ :=
  1 / (4 * κ ^ 2)

/-- The integer count selected from the inverse-square angle. -/
noncomputable def aaRoundCount (κ : ℝ) : ℕ :=
  ⌊Real.pi / (4 * Real.arcsin (Real.sqrt (inverseSquareParameter κ)))⌋₊

lemma inverseSquareParameter_pos {κ : ℝ} (hkappa_pos : 0 < κ) :
    0 < inverseSquareParameter κ := by
  unfold inverseSquareParameter
  positivity

lemma inverseSquareParameter_le_third {κ : ℝ} (hkappa_ge_one : 1 ≤ κ) :
    inverseSquareParameter κ ≤ 1 / 3 := by
  unfold inverseSquareParameter
  have hkappa_sq_ge_one : (1 : ℝ) ≤ κ ^ 2 := by nlinarith
  have hden_pos : 0 < 4 * κ ^ 2 := by nlinarith
  rw [one_div_le_one_div hden_pos (by norm_num : (0 : ℝ) < 3)]
  nlinarith

/-- A real-valued candidate cost expression, unconnected to execution events. -/
noncomputable def linearSystemCostExpression (N s : ℕ) (κ ε : ℝ) : ℝ :=
  (κ ^ 2) * ((s : ℝ) ^ 2) * Real.log ((N : ℝ) + 1) * ((1 : ℝ) / ε) *
    (Real.log (κ / ε)) ^ 2

/-- Nonnegativity of the candidate cost expression for positive error tolerance. -/
lemma linearSystemCostExpression_nonneg {N s : ℕ} (κ ε : ℝ) (_hkappa_pos : 0 < κ)
    (heps_pos : 0 < ε) :
    linearSystemCostExpression N s κ ε ≥ 0 := by
  unfold linearSystemCostExpression
  have h_sq : 0 ≤ (κ : ℝ) ^ 2 := pow_two_nonneg _
  have h_s_sq : 0 ≤ (s : ℝ) ^ 2 := pow_two_nonneg _
  have h_one_le : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    exact_mod_cast (show 1 ≤ N + 1 from Nat.le_add_left 1 N)
  have h_log : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg h_one_le
  have h_inv_eps : 0 ≤ (1 : ℝ) / ε := div_nonneg (by norm_num) heps_pos.le
  have h_log2 : 0 ≤ (Real.log (κ / ε)) ^ 2 := pow_two_nonneg _
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h_sq h_s_sq) h_log) h_inv_eps) h_log2

/-- The planar trigonometric expression is at least `2/3` at the selected inverse-square angle. -/
lemma inverseSquare_rotation_bound (κ : ℝ) (hkappa_ge_one : 1 ≤ κ) :
    Real.sin (((2 : ℝ) * (aaRoundCount κ : ℝ) + 1) *
        Real.arcsin (Real.sqrt (inverseSquareParameter κ))) ^ 2 ≥ 2 / 3 := by
  apply AmplitudeAmplification.aa_success_ge_two_thirds
  · exact inverseSquareParameter_pos (lt_of_lt_of_le zero_lt_one hkappa_ge_one)
  · exact inverseSquareParameter_le_third hkappa_ge_one
  · rfl

end QuantumAlg.LinearSystem
