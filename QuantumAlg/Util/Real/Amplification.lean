/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Integer iteration bounds for planar rotations

The bounds concern the trigonometric expression at an explicitly chosen angle and integer count.
-/

@[expose] public section

namespace QuantumAlg.AmplitudeAmplification

/-- `x ≤ arcsin x` for `0 ≤ x ≤ 1`. Proved via `Real.sin_le` and `Real.le_arcsin_iff_sin_le`. -/
lemma arcsin_ge_self {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) : x ≤ Real.arcsin x := by
  have hx_pi_ub : x ≤ Real.pi / 2 := by
    have h_pi_gt_two : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
    have : (1 : ℝ) < Real.pi / 2 := by linarith
    linarith
  have hx_mem_angle : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    exact ⟨by nlinarith, hx_pi_ub⟩
  have hx_mem_unit : x ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ⟨by nlinarith, hx₁⟩
  rw [Real.le_arcsin_iff_sin_le hx_mem_angle hx_mem_unit]
  exact Real.sin_le hx₀

/-- Classical AA bound: with optimal `k = ⌊π/(4θ)⌋` iterations,
`sin²((2k+1)·θ) ≥ 1 - ε` where `θ = arcsin(√ε)`.

Proof via sin monotonicity on `[-π/2,π/2]` and symmetry `sin(π-x) = sin x`. -/
lemma exact_aa_success_prob_ge (ε : ℝ) (hε_pos : 0 < ε) (hε_le_one : ε ≤ 1) (k : ℕ)
    (hk : (k : ℝ) = ⌊Real.pi / (4 * Real.arcsin (Real.sqrt ε))⌋₊) :
    Real.sin (((2 : ℝ) * (k : ℝ) + 1) * Real.arcsin (Real.sqrt ε)) ^ 2 ≥ 1 - ε := by
  let θ := Real.arcsin (Real.sqrt ε)
  have h_sqrt_nonneg : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  have h_sqrt_le_one : Real.sqrt ε ≤ 1 := (Real.sqrt_le_one).mpr hε_le_one
  have h_sqrt_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε_pos
  have hθ_pos : 0 < θ := Real.arcsin_pos.mpr h_sqrt_pos
  have hθ_sin : Real.sin θ = Real.sqrt ε := Real.sin_arcsin (by nlinarith) h_sqrt_le_one
  -- floor bounds: k ≤ π/(4θ) < k+1
  have hk_lb : (k : ℝ) ≤ Real.pi / (4 * θ) := by
    rw [hk]; exact mod_cast Nat.floor_le (by positivity : 0 ≤ Real.pi / (4 * θ))
  have hk_ub : Real.pi / (4 * θ) < (k : ℝ) + 1 := by
    rw [hk]; exact mod_cast Nat.lt_floor_add_one (Real.pi / (4 * θ))
  let a := ((2 : ℝ) * (k : ℝ) + 1) * θ
  -- a = (2k+1)·θ ∈ (π/2 - θ, π/2 + θ] via hk_lb, hk_ub
  have ha_ub : a ≤ Real.pi / 2 + θ := by
    dsimp [a]
    calc
      (2 * (k : ℝ) + 1) * θ = 2 * (k : ℝ) * θ + θ := by ring
      _ ≤ 2 * (Real.pi / (4 * θ)) * θ + θ := by nlinarith
      _ = Real.pi / 2 + θ := by field_simp [hθ_pos.ne.symm]; ring
  have ha_lb : Real.pi / 2 - θ < a := by
    dsimp [a]
    calc
      Real.pi / 2 - θ = 2 * (Real.pi / (4 * θ)) * θ - θ := by
        field_simp [hθ_pos.ne.symm]; ring
      _ < 2 * ((k : ℝ) + 1) * θ - θ := by nlinarith
      _ = (2 * (k : ℝ) + 1) * θ := by ring
  -- Key: sin²(a) ≥ sin²(π/2 - θ) = cos²θ = 1 - ε
  have hθ_pi_le : θ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have h_sq_ge : Real.sin a ^ 2 ≥ (Real.sin (Real.pi / 2 - θ)) ^ 2 := by
    by_cases ha_le_pi2 : a ≤ Real.pi / 2
    · -- Case a ∈ [π/2 - θ, π/2]: sin is increasing on [-π/2, π/2]
      have h_lower : -(Real.pi / 2) ≤ Real.pi / 2 - θ := by
        have : θ ≤ Real.pi := by linarith [hθ_pi_le, Real.pi_pos]
        linarith
      have h_lower_a : Real.pi / 2 - θ ≤ a := by linarith
      have h_upper_a : a ≤ Real.pi / 2 := ha_le_pi2
      have h_sin_le : Real.sin (Real.pi / 2 - θ) ≤ Real.sin a :=
        Real.sin_le_sin_of_le_of_le_pi_div_two h_lower h_upper_a h_lower_a
      have h_nonneg_l : 0 ≤ Real.sin (Real.pi / 2 - θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
      have h_nonneg_r : 0 ≤ Real.sin a :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      nlinarith
    · -- Case a ∈ [π/2, π/2 + θ]: use symmetry sin(π - a) = sin a
      let b := Real.pi - a
      have hb_lower : Real.pi / 2 - θ ≤ b := by dsimp [b]; linarith
      have hb_upper : b ≤ Real.pi / 2 := by dsimp [b]; linarith
      have h_sin_eq : Real.sin a = Real.sin b := by rw [Real.sin_pi_sub]
      have h_sin_le_b : Real.sin (Real.pi / 2 - θ) ≤ Real.sin b :=
        Real.sin_le_sin_of_le_of_le_pi_div_two
          (by
            have : θ ≤ Real.pi := by linarith [hθ_pi_le, Real.pi_pos]
            linarith)
          hb_upper hb_lower
      have h_nonneg_l : 0 ≤ Real.sin (Real.pi / 2 - θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ_pi_le]) (by nlinarith)
      have h_nonneg_b : 0 ≤ Real.sin b :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by dsimp [b]; nlinarith) (by dsimp [b]; nlinarith)
      rw [h_sin_eq]
      nlinarith
  -- sin(π/2 - θ) = cos θ
  have h_sin_cos : Real.sin (Real.pi / 2 - θ) = Real.cos θ := by
    rw [Real.sin_pi_div_two_sub]
  rw [h_sin_cos] at h_sq_ge
  -- cos²θ = 1 - sin²θ = 1 - (√ε)² = 1 - ε
  have h_cos_sq_eq : Real.cos θ ^ 2 = 1 - ε := by
    have h := Real.cos_sq_add_sin_sq θ
    rw [hθ_sin] at h
    rw [Real.sq_sqrt hε_pos.le] at h
    linarith
  rw [h_cos_sq_eq] at h_sq_ge
  exact h_sq_ge

/-- Success probability ≥ 2/3 for `ε ≤ 1/3`. Corollary of `exact_aa_success_prob_ge`. -/
lemma aa_success_ge_two_thirds (ε : ℝ) (hε_pos : 0 < ε) (hε_le_third : ε ≤ 1 / 3)
    (k : ℕ) (hk : (k : ℝ) = ⌊Real.pi / (4 * Real.arcsin (Real.sqrt ε))⌋₊) :
    Real.sin (((2 : ℝ) * (k : ℝ) + 1) * Real.arcsin (Real.sqrt ε)) ^ 2 ≥ 2/3 := by
  have h := exact_aa_success_prob_ge ε hε_pos (by linarith) k hk
  linarith


end QuantumAlg.AmplitudeAmplification
