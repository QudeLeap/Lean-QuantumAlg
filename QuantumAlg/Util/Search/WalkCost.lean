/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Rounded search-cost expressions

These are arithmetic bounds; execution counts require a separate derivation from a program.
-/

@[expose] public section

namespace QuantumAlg

open scoped Real

noncomputable section

lemma binaryLog_nonneg_of_one_le {X : ℝ} (hX : 1 ≤ X) : 0 ≤ Real.logb 2 X := by
  rw [Real.logb, div_eq_mul_inv]
  refine mul_nonneg (Real.log_nonneg hX) (by positivity : 0 ≤ (Real.log 2)⁻¹)

lemma binaryPower_ceil_log_lt (X : ℝ) (hX : 1 ≤ X) :
    (2 : ℝ) ^ (⌈Real.logb 2 X⌉₊ : ℝ) < 2 * X := by
  have h_log_nonneg : 0 ≤ Real.logb 2 X := by
    apply Real.logb_nonneg (by norm_num : 1 < (2 : ℝ)) hX
  have h_ceil := Nat.ceil_lt_add_one h_log_nonneg
  have h_mono := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1 < (2 : ℝ)) h_ceil
  rw [Real.rpow_add (by norm_num)] at h_mono
  rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith : 0 < X)] at h_mono
  rw [Real.rpow_one] at h_mono
  linarith

/-- Scalar cost expression: setup plus rounds of checks and repeated updates. -/
def walkCost (S C U t₁ t₂ : ℕ) : ℕ :=
  S + t₁ * (C + (2 ^ t₂) * U)

/-- Rounding bounds for a scalar cost expression under explicit parameter assumptions. -/
lemma walkCost_le_of_parameters
    (S C U : ℕ) (ε δ η : ℝ) (hε_pos : 0 < ε) (_hδ_pos : 0 < δ) (_hη_pos : 0 < η)
    (h_ratio_ge_one : 1 ≤ π / Real.sqrt (2 * η * δ)) :
    let t₁ := Nat.ceil (π / (4 * Real.sqrt ε))
    let t₂ := Nat.ceil (Real.logb 2 (π / Real.sqrt (2 * η * δ)))
    ((walkCost S C U t₁ t₂) : ℝ) ≤
      (S : ℝ) + (π / (4 * Real.sqrt ε) + 1) *
        ((C : ℝ) + (2 * π / Real.sqrt (2 * η * δ)) * (U : ℝ)) := by
  intro t₁ t₂
  unfold walkCost
  push_cast
  have h_t₁_lt : (t₁ : ℝ) < π / (4 * Real.sqrt ε) + 1 := by
    dsimp [t₁]
    have h_arg_nonneg : 0 ≤ π / (4 * Real.sqrt ε) := by positivity
    exact Nat.ceil_lt_add_one h_arg_nonneg
  have h_t₂_lt : ((2 : ℝ) ^ t₂) < (2 * π / Real.sqrt (2 * η * δ)) := by
    dsimp [t₂]
    have h := binaryPower_ceil_log_lt (π / Real.sqrt (2 * η * δ)) h_ratio_ge_one
    rw [Real.rpow_natCast] at h
    rw [← mul_div_assoc] at h
    exact h
  apply add_le_add_right
  apply mul_le_mul h_t₁_lt.le
  · apply add_le_add_right
    apply mul_le_mul_of_nonneg_right h_t₂_lt.le
    positivity
  · positivity
  · positivity

end
end QuantumAlg
