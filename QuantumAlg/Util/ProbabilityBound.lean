/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.Norm

/-!
# State distance to measurement probability
-/

@[expose] public section

namespace QuantumAlg

open scoped Real
open Complex

lemma success_probability_bound_of_dist {ι : Type*} [Fintype ι]
    (G ψ φ : EuclideanSpace ℂ ι) (ε : ℝ)
    (hG_norm : ‖G‖ = 1) (hψ_norm : ‖ψ‖ = 1) (hφ_norm : ‖φ‖ = 1)
    (h_dist : ‖ψ - φ‖ ≤ ε) :
    Complex.normSq (inner ℂ G ψ) ≥ Complex.normSq (inner ℂ G φ) - 2 * ε := by
  have hGφ_norm : ‖inner ℂ G φ‖ ≤ 1 := by
    calc
      ‖inner ℂ G φ‖ ≤ ‖G‖ * ‖φ‖ := norm_inner_le_norm _ _
      _ = 1 := by simp [hG_norm, hφ_norm]
  have hGψ_norm : ‖inner ℂ G ψ‖ ≤ 1 := by
    calc
      ‖inner ℂ G ψ‖ ≤ ‖G‖ * ‖ψ‖ := norm_inner_le_norm _ _
      _ = 1 := by simp [hG_norm, hψ_norm]
  have h_inner_diff : ‖inner ℂ G ψ - inner ℂ G φ‖ ≤ ε := by
    calc
      ‖inner ℂ G ψ - inner ℂ G φ‖ = ‖inner ℂ G (ψ - φ)‖ := by rw [inner_sub_right]
      _ ≤ ‖G‖ * ‖ψ - φ‖ := norm_inner_le_norm _ _
      _ = ‖ψ - φ‖ := by simp [hG_norm]
      _ ≤ ε := h_dist
  have h_norm_diff : |‖inner ℂ G ψ‖ - ‖inner ℂ G φ‖| ≤ ε :=
    le_trans (abs_norm_sub_norm_le _ _) h_inner_diff
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  set a := ‖inner ℂ G ψ‖
  set b := ‖inner ℂ G φ‖
  have ha_sq_sub_b_sq : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  have h_sum_le_two : a + b ≤ 2 := by linarith
  have h_nonneg_sum : 0 ≤ a + b := by positivity
  have h_abs_le' : a - b ≤ ε := (abs_le.mp h_norm_diff).right
  have h_abs_ge : -ε ≤ a - b := (abs_le.mp h_norm_diff).left
  have h_eps_nonneg : 0 ≤ ε := by
    linarith [abs_nonneg (a - b), h_norm_diff]
  have h_a_ge_b_sub_eps : a ≥ b - ε := by linarith
  have h_bound : b ^ 2 - a ^ 2 ≤ 2 * ε := by
    have h_neg_sq : b ^ 2 - a ^ 2 = -(a ^ 2 - b ^ 2) := by ring
    rw [h_neg_sq, ha_sq_sub_b_sq]
    have : -(a - b) ≤ ε := by linarith
    have h_mul : (-(a - b)) * (a + b) ≤ ε * 2 := by
      have h1 : (-(a - b)) * (a + b) ≤ ε * (a + b) :=
        mul_le_mul_of_nonneg_right this h_nonneg_sum
      have h2 : ε * (a + b) ≤ ε * 2 :=
        mul_le_mul_of_nonneg_left h_sum_le_two h_eps_nonneg
      linarith
    linarith
  linarith

end QuantumAlg
