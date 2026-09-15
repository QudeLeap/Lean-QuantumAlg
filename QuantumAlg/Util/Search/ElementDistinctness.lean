/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.Search.WalkCost
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Element-distinctness cost arithmetic

Conditional scalar inequalities motivated by subset search [dW19, qcnotes.tex:3342-3377].
-/

@[expose] public section

namespace QuantumAlg

open scoped Real
open Real

noncomputable section

variable {N r : ℕ}

/-! ### Problem definition -/

/-- A collision exists if two distinct inputs have the same image. -/
def HasCollision {N M : ℕ} (f : Fin N → Fin M) : Prop :=
  ∃ i j : Fin N, i ≠ j ∧ f i = f j

/-! ### Numerical parameters

The inequalities below are explicit scalar assumptions. A `SearchCostParameters`
value alone does not identify a transition matrix or a marked event. -/

/-- Numerical gap and fraction parameters satisfying explicit bounds. -/
structure SearchCostParameters (N r : ℕ) where
  /-- Positive-gap parameter when `r > 0`. -/
  spectralGap : ℝ
  gap_lower_bound : spectralGap ≥ 1 / (r : ℝ)
  gap_upper_bound : spectralGap ≤ 1
  /-- Fraction parameter subject to the lower-bound assumption. -/
  markedFraction : ℝ
  /-- Relaxed lower bound: ε ≥ (1/2)·(r/N)². The exact formula
  `ε = r(r-1)/(N(N-1))` does not satisfy the stronger `ε ≥ (r/N)²`.
  The factor 1/2 is an explicit assumption on this numerical expression. -/
  fraction_lower_bound : markedFraction ≥ (1/2 : ℝ) * (((r : ℝ) / (N : ℝ)) ^ 2)

/-- A numerical instance saturating the chosen lower bounds; no graph realization is asserted. -/
def standardSearchCostParameters (N r : ℕ) : SearchCostParameters N r :=
  ⟨1 / (r : ℝ), le_rfl,
    by
      -- 1/r ≤ 1: true for any r (1/r ≤ 1 iff 1 ≤ r, or r = 0 where 1/0 = 0 ≤ 1)
      by_cases hr : r = 0
      · subst r; simp
      · have hr_pos : 0 < (r : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hr
        have hr_ge_one : (1 : ℝ) ≤ (r : ℝ) := by
          exact_mod_cast Nat.one_le_of_lt (Nat.pos_of_ne_zero hr)
        exact (div_le_one hr_pos).mpr hr_ge_one,
    (1/2 : ℝ) * (((r : ℝ) / (N : ℝ)) ^ 2), le_rfl⟩

namespace SearchCostParameters

variable {N r : ℕ} (p : SearchCostParameters N r)

lemma spectralGap_pos (_hNpos : 0 < N) (hrpos : 0 < r) : 0 < p.spectralGap := by
  have h := p.gap_lower_bound
  have hpos : 0 < 1 / (r : ℝ) := div_pos (by norm_num) (by exact_mod_cast hrpos)
  linarith

lemma markedFraction_pos (hNpos : 0 < N) (hrpos : 0 < r) : 0 < p.markedFraction := by
  have hpos : 0 < ((r : ℝ) / (N : ℝ)) ^ 2 := by positivity
  have h := p.fraction_lower_bound
  linarith

lemma sqrt_markedFraction_ge (hNpos : 0 < N) (hrpos : 0 < r) :
    Real.sqrt p.markedFraction ≥ ((r : ℝ) / (N : ℝ)) / Real.sqrt 2 := by
  have h_nonneg_rN : 0 ≤ (r : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h_sq : (1/2 : ℝ) * (((r : ℝ) / (N : ℝ)) ^ 2) ≤ p.markedFraction := p.fraction_lower_bound
  calc
    ((r : ℝ) / (N : ℝ)) / Real.sqrt 2
        = Real.sqrt (((r : ℝ) / (N : ℝ)) ^ 2) / Real.sqrt 2 := by rw [Real.sqrt_sq h_nonneg_rN]
    _ = Real.sqrt ((((r : ℝ) / (N : ℝ)) ^ 2) / 2) := by rw [Real.sqrt_div (by positivity) _]
    _ = Real.sqrt ((1/2 : ℝ) * (((r : ℝ) / (N : ℝ)) ^ 2)) := by ring
    _ ≤ Real.sqrt p.markedFraction := Real.sqrt_le_sqrt h_sq

lemma sqrt_spectralGap_div_bound (hNpos : 0 < N) (hrpos : 0 < r) :
    1 / Real.sqrt p.spectralGap ≤ Real.sqrt (r : ℝ) := by
  have hpos_gap : 0 < p.spectralGap := p.spectralGap_pos hNpos hrpos
  have hpos_sqrt_gap : 0 < Real.sqrt p.spectralGap := Real.sqrt_pos.mpr hpos_gap
  have h_sqrt_r : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hrpos)
  have h_sqrt_gap_ge : 1 / Real.sqrt (r : ℝ) ≤ Real.sqrt p.spectralGap := by
    calc
      1 / Real.sqrt (r : ℝ) = Real.sqrt (1 / (r : ℝ)) := by
        rw [Real.sqrt_div (by norm_num) _]; simp
      _ ≤ Real.sqrt p.spectralGap :=
        Real.sqrt_le_sqrt p.gap_lower_bound
  -- From 1/√r ≤ √gap, take reciprocals to get 1/√gap ≤ √r
  have h_recip : 1 / Real.sqrt p.spectralGap ≤ 1 / (1 / Real.sqrt (r : ℝ)) :=
    (one_div_le_one_div hpos_sqrt_gap (by positivity)).mpr h_sqrt_gap_ge
  simpa [div_div] using h_recip

end SearchCostParameters

/-! ### Numerical gap condition for the scalar estimate -/

private lemma ratio_condition {r : ℕ} (hrpos : 0 < r) (δ : ℝ) (hδ_bound : δ ≥ 1 / (r : ℝ))
    (hδ_le_one : δ ≤ 1) :
    (1 : ℝ) ≤ Real.pi / Real.sqrt (2 * ((1 : ℝ) / 2) * δ) := by
  have h_sqrt : Real.sqrt (2 * ((1 : ℝ) / 2) * δ) = Real.sqrt δ := by ring
  rw [h_sqrt]
  have hsqrt_pos : 0 < Real.sqrt δ := Real.sqrt_pos.mpr (by
    have : 0 < 1 / (r : ℝ) := div_pos (by norm_num) (by exact_mod_cast hrpos)
    linarith)
  have hsqrt_le_one : Real.sqrt δ ≤ 1 := Real.sqrt_le_one.mpr hδ_le_one
  have h_one_lt_pi : (1 : ℝ) < Real.pi := by
    have : (3 : ℝ) < Real.pi := Real.pi_gt_three
    linarith
  have hsqrt_le_pi : Real.sqrt δ ≤ Real.pi := le_trans hsqrt_le_one (by linarith)
  -- Goal: 1 ≤ π / √δ. Since √δ ≤ π and both > 0:
  -- 1/π ≤ 1/√δ (taking reciprocal), then multiply by π
  have h_recip : 1 / Real.pi ≤ 1 / Real.sqrt δ :=
    (one_div_le_one_div Real.pi_pos hsqrt_pos).mpr hsqrt_le_pi
  calc
    (1 : ℝ) = Real.pi * (1 / Real.pi) := by field_simp [ne_of_gt Real.pi_pos]
    _ ≤ Real.pi * (1 / Real.sqrt δ) := mul_le_mul_of_nonneg_left h_recip (by positivity)
    _ = Real.pi / Real.sqrt δ := by ring

/-! ### Main walk-time bound -/

/-- Conditional bound on the rounded scalar expression with setup `r+1`, check `0`, and update
  `1`. -/
theorem elementDistinctness_costExpression_le (hNpos : 0 < N) (hrpos : 0 < r)
    (p : SearchCostParameters N r) :
    let t₁ := Nat.ceil (Real.pi / (4 * Real.sqrt p.markedFraction))
    let t₂ := Nat.ceil (Real.logb 2 (Real.pi / Real.sqrt (2 * ((1 : ℝ) / 2) * p.spectralGap)))
    ((walkCost (r+1) 0 1 t₁ t₂) : ℝ)
      ≤ ((r+1 : ℕ) : ℝ) + (Real.pi * Real.sqrt 2 * (N : ℝ) / (4 * (r : ℝ)) + 1) *
        (2 * Real.pi * Real.sqrt (r : ℝ)) := by
  intro t₁ t₂
  have hε_pos : 0 < p.markedFraction := p.markedFraction_pos hNpos hrpos
  have hδ_pos : 0 < p.spectralGap := p.spectralGap_pos hNpos hrpos
  have hη_pos : 0 < (1 : ℝ) / 2 := by norm_num
  have h_ratio : (1 : ℝ) ≤ Real.pi/ Real.sqrt (2 * ((1 : ℝ) / 2) * p.spectralGap) :=
    ratio_condition hrpos p.spectralGap p.gap_lower_bound p.gap_upper_bound
  have h_main := walkCost_le_of_parameters (r+1) 0 1 p.markedFraction p.spectralGap
    ((1 : ℝ) / 2) hε_pos hδ_pos hη_pos h_ratio
  -- h_main gives: walk ≤ (r+1) + (π/(4√ε) + 1)*(0 + (2π/√(2ηδ))*1)
  -- Simplify RHS: 0 + (2π/√δ)*1 = 2π/√δ, and 2*(1/2)*δ = δ
  -- So: walk ≤ (r+1) + (π/(4√ε) + 1)*(2π/√δ)
  --
  -- We need: walk ≤ (r+1) + (π√2·N/(4r) + 1)*(2π√r)
  --
  -- By comparing product terms: (π/(4√ε) + 1)*(2π/√δ) ≤ (π√2·N/(4r) + 1)*(2π√r)
  -- using √ε ≥ (r/N)/√2 and 1/√δ ≤ √r from SearchCostParameters
  have h_walk_bound : ((walkCost (r+1) 0 1 t₁ t₂) : ℝ) ≤
      ((r+1 : ℕ) : ℝ) + (Real.pi / (4 * Real.sqrt p.markedFraction) + 1) *
      (2 * Real.pi / Real.sqrt p.spectralGap) := by
    -- h_main gives the bound with unsimplified RHS
    refine le_trans h_main ?_
    simp
  have h_prod_bound :
      (Real.pi / (4 * Real.sqrt p.markedFraction) + 1)
          * (2 * Real.pi / Real.sqrt p.spectralGap)
        ≤ (Real.pi * Real.sqrt 2 * (N : ℝ) / (4 * (r : ℝ)) + 1)
          * (2 * Real.pi * Real.sqrt (r : ℝ)) := by
    have h_term1 : Real.pi / (4 * Real.sqrt p.markedFraction) ≤
        Real.pi * Real.sqrt 2 * (N : ℝ) / (4 * (r : ℝ)) := by
      have h_inv : 1 / Real.sqrt p.markedFraction ≤ Real.sqrt 2 * (N : ℝ) / (r : ℝ) := by
        have h_ge : Real.sqrt p.markedFraction ≥ ((r : ℝ) / (N : ℝ)) / Real.sqrt 2 :=
          p.sqrt_markedFraction_ge hNpos hrpos
        have hpos_sqrt := Real.sqrt_pos.mpr hε_pos
        have hpos_div : 0 < ((r : ℝ) / (N : ℝ)) / Real.sqrt 2 := by positivity
        have h_recip := (one_div_le_one_div hpos_sqrt hpos_div).mpr h_ge
        -- Simplify RHS: 1 / ((r/N)/√2) = √2·N/r
        have h_simplify : 1 / (((r : ℝ) / (N : ℝ)) / Real.sqrt 2) =
            Real.sqrt 2 * (N : ℝ) / (r : ℝ) := by
          field_simp [show (r : ℝ) ≠ 0 from by positivity, show (N : ℝ) ≠ 0 from by positivity,
            show Real.sqrt 2 ≠ 0 from by positivity]
        simpa [h_simplify] using h_recip
      have h_pi_four_pos : 0 ≤ Real.pi / 4 := by positivity
      calc
        Real.pi / (4 * Real.sqrt p.markedFraction)
            = (Real.pi / 4) * (1 / Real.sqrt p.markedFraction) := by ring
        _ ≤ (Real.pi / 4) * (Real.sqrt 2 * (N : ℝ) / (r : ℝ)) :=
          mul_le_mul_of_nonneg_left h_inv h_pi_four_pos
        _ = Real.pi * Real.sqrt 2 * (N : ℝ) / (4 * (r : ℝ)) := by ring
    have h_term2 :
        2 * Real.pi / Real.sqrt p.spectralGap ≤ 2 * Real.pi * Real.sqrt (r : ℝ) := by
      have h := p.sqrt_spectralGap_div_bound hNpos hrpos
      calc
        2 * Real.pi / Real.sqrt p.spectralGap
            = (2 * Real.pi) * (1 / Real.sqrt p.spectralGap) := by ring
        _ ≤ (2 * Real.pi) * Real.sqrt (r : ℝ) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = 2 * Real.pi * Real.sqrt (r : ℝ) := by ring
    have h_f1 : Real.pi / (4 * Real.sqrt p.markedFraction) + 1 ≤
        Real.pi * Real.sqrt 2 * (N : ℝ) / (4 * (r : ℝ)) + 1 := by linarith
    have h_nonneg_f1 : 0 ≤ Real.pi / (4 * Real.sqrt p.markedFraction) + 1 := by positivity
    have h_nonneg_t2 : 0 ≤ 2 * Real.pi / Real.sqrt p.spectralGap := by positivity
    have h_nonneg_f1b : 0 ≤ Real.pi * Real.sqrt 2 * (N : ℝ) / (4 * (r : ℝ)) + 1 := by positivity
    exact mul_le_mul h_f1 h_term2 h_nonneg_t2 h_nonneg_f1b
  -- Combine: walk ≤ (r+1) + product1 ≤ (r+1) + product2 = target
  have h_add :
      ((r+1 : ℕ) : ℝ)
        + (Real.pi / (4 * Real.sqrt p.markedFraction) + 1)
          * (2 * Real.pi / Real.sqrt p.spectralGap)
      ≤ ((r+1 : ℕ) : ℝ)
        + (Real.pi * Real.sqrt 2 * (N : ℝ) / (4 * (r : ℝ)) + 1)
          * (2 * Real.pi * Real.sqrt (r : ℝ)) := by
    linarith
  exact le_trans h_walk_bound h_add

end
end QuantumAlg
