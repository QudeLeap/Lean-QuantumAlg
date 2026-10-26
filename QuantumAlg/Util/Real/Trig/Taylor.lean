/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rational Taylor approximations to sine and cosine

The real and imaginary parts of the exponential polynomial are evaluated over
the rationals. Soundness follows from Mathlib's complex exponential remainder.
-/

@[expose] public section

namespace QuantumAlg.TrigEnclosure

open Finset

/-- Real coefficient of a power of the imaginary unit. -/
def cosCoeff (k : ℕ) : ℚ := if k % 4 = 0 then 1 else if k % 4 = 2 then -1 else 0

/-- Imaginary coefficient of a power of the imaginary unit. -/
def sinCoeff (k : ℕ) : ℚ := if k % 4 = 1 then 1 else if k % 4 = 3 then -1 else 0

/-- Real part of the exponential Taylor polynomial with `N` terms. -/
def cosPoly (q : ℚ) (N : ℕ) : ℚ := ∑ k ∈ range N, cosCoeff k * q ^ k / k.factorial

/-- Imaginary part of the exponential Taylor polynomial with `N` terms. -/
def sinPoly (q : ℚ) (N : ℕ) : ℚ := ∑ k ∈ range N, sinCoeff k * q ^ k / k.factorial

private lemma cosCoeff_cast (k : ℕ) : (cosCoeff k : ℝ) = (Complex.I ^ k).re := by
  rw [Complex.I_pow_eq_pow_mod]
  have h : k % 4 < 4 := Nat.mod_lt _ (by decide)
  unfold cosCoeff
  interval_cases hk : k % 4 <;> norm_num

private lemma sinCoeff_cast (k : ℕ) : (sinCoeff k : ℝ) = (Complex.I ^ k).im := by
  rw [Complex.I_pow_eq_pow_mod]
  have h : k % 4 < 4 := Nat.mod_lt _ (by decide)
  unfold sinCoeff
  interval_cases hk : k % 4 <;> norm_num

private lemma cosPoly_cast (q : ℚ) (N : ℕ) :
    (cosPoly q N : ℝ) =
      (∑ k ∈ range N, (((q : ℝ) : ℂ) * Complex.I) ^ k / k.factorial).re := by
  simp only [cosPoly, Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, Complex.re_sum, Complex.div_natCast_re, mul_pow]
  apply sum_congr rfl
  intro k _
  rw [cosCoeff_cast]
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  ring

private lemma sinPoly_cast (q : ℚ) (N : ℕ) :
    (sinPoly q N : ℝ) =
      (∑ k ∈ range N, (((q : ℝ) : ℂ) * Complex.I) ^ k / k.factorial).im := by
  simp only [sinPoly, Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, Complex.im_sum, Complex.div_natCast_im, mul_pow]
  apply sum_congr rfl
  intro k _
  rw [sinCoeff_cast]
  rw [← Complex.ofReal_pow, Complex.im_ofReal_mul]
  ring

private lemma exp_poly_error (q : ℚ) (N : ℕ) (hq : |(q : ℝ)| ≤ 1) (hN : 0 < N) :
    ‖Complex.exp (((q : ℝ) : ℂ) * Complex.I) -
      ∑ k ∈ range N, (((q : ℝ) : ℂ) * Complex.I) ^ k / k.factorial‖ ≤
        2 / (N.factorial : ℝ) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnorm : ‖((q : ℝ) : ℂ) * Complex.I‖ ≤ 1 := by simpa using hq
  have h := Complex.exp_bound' (n := N) (x := ((q : ℝ) : ℂ) * Complex.I) (by
    apply (div_le_iff₀ (by positivity)).mpr
    simp only [Nat.cast_succ]
    linarith)
  apply h.trans
  have hp := pow_le_one₀ (norm_nonneg _) hnorm (n := N)
  calc
    _ ≤ 1 / (N.factorial : ℝ) * 2 := by gcongr
    _ = _ := by ring

/-- Uniform rational cosine remainder on the unit interval. -/
lemma cosPoly_error (q : ℚ) (N : ℕ) (hq : |(q : ℝ)| ≤ 1) (hN : 0 < N) :
    |Real.cos q - (cosPoly q N : ℝ)| ≤ 2 / (N.factorial : ℝ) := by
  have h := (Complex.abs_re_le_norm _).trans (exp_poly_error q N hq hN)
  rw [Complex.sub_re, ← cosPoly_cast, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin] at h
  simpa only [Complex.add_re, Complex.mul_I_re, Complex.ofReal_re,
    Complex.ofReal_im, neg_zero, add_zero] using h

/-- Uniform rational sine remainder on the unit interval. -/
lemma sinPoly_error (q : ℚ) (N : ℕ) (hq : |(q : ℝ)| ≤ 1) (hN : 0 < N) :
    |Real.sin q - (sinPoly q N : ℝ)| ≤ 2 / (N.factorial : ℝ) := by
  have h := (Complex.abs_im_le_norm _).trans (exp_poly_error q N hq hN)
  rw [Complex.sub_im, ← sinPoly_cast, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin] at h
  simpa only [Complex.add_im, Complex.mul_I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_add] using h

end QuantumAlg.TrigEnclosure
