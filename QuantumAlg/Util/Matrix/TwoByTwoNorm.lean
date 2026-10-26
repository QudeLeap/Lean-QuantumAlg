/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Entrywise bounds for the two-dimensional L2 operator norm

The norm instance is scoped locally, matching the L2 norm on Euclidean space.
No global matrix norm instance is installed.
-/

@[expose] public section

namespace QuantumAlg.MatrixBounds

open scoped Matrix.Norms.L2Operator

private lemma row_norm_sq_le (a b x y : ℂ) :
    ‖a * x + b * y‖ ^ 2 ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have h := norm_add_le (a * x) (b * y)
  simp only [norm_mul] at h
  have hs : ‖a * x + b * y‖ ^ 2 ≤ (‖a‖ * ‖x‖ + ‖b‖ * ‖y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖ * ‖y‖ - ‖b‖ * ‖x‖)]

/-- The L2 operator norm is bounded by the Frobenius norm. -/
lemma opNorm_le_frobenius (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  simp only [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h0 := row_norm_sq_le (A 0 0) (A 0 1) (x 0) (x 1)
  have h1 := row_norm_sq_le (A 1 0) (A 1 1) (x 0) (x 1)
  nlinarith

/-- Any common entrywise absolute bound gives twice that bound on the L2 norm. -/
lemma opNorm_le_two_mul_max_abs (A : Matrix (Fin 2) (Fin 2) ℂ) (M : ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ M) : ‖A‖ ≤ 2 * M := by
  have hM : 0 ≤ M := (norm_nonneg (A 0 0)).trans (h 0 0)
  apply (opNorm_le_frobenius A).trans
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · have hs (i j) := pow_le_pow_left₀ (norm_nonneg (A i j)) (h i j) 2
    simp only [Fin.sum_univ_two]
    nlinarith [hs 0 0, hs 0 1, hs 1 0, hs 1 1]

private lemma abs_sub_le_endpoints (a b l u p q : ℝ)
    (ha : l ≤ a) (ha' : a ≤ u) (hb : p ≤ b) (hb' : b ≤ q) :
    |a - b| ≤ max |l - q| |u - p| := by
  apply abs_le.mpr
  constructor
  · have := le_abs_self (q - l)
    rw [abs_sub_comm q l] at this
    have := le_max_left |l - q| |u - p|
    linarith
  · have := le_abs_self (u - p)
    have := le_max_right |l - q| |u - p|
    linarith

/-- Enclosed real and imaginary coordinates give a Euclidean complex-error bound. -/
lemma norm_sub_le_interval (a : ℂ) (c s : ℝ)
    (arLo arHi aiLo aiHi cLo cHi sLo sHi : ℚ)
    (har : (arLo : ℝ) ≤ a.re) (har' : a.re ≤ (arHi : ℝ))
    (hai : (aiLo : ℝ) ≤ a.im) (hai' : a.im ≤ (aiHi : ℝ))
    (hc : (cLo : ℝ) ≤ c) (hc' : c ≤ (cHi : ℝ))
    (hs : (sLo : ℝ) ≤ s) (hs' : s ≤ (sHi : ℝ)) :
    ‖a - ((c : ℂ) + Complex.I * s)‖ ≤
      Real.sqrt (((max |arLo - cHi| |arHi - cLo| : ℚ) : ℝ) ^ 2 +
        ((max |aiLo - sHi| |aiHi - sLo| : ℚ) : ℝ) ^ 2) := by
  have hr := abs_sub_le_endpoints a.re c arLo arHi cLo cHi har har' hc hc'
  have hi := abs_sub_le_endpoints a.im s aiLo aiHi sLo sHi hai hai' hs hs'
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero,
    add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, one_mul, zero_add]
  have hr2 := pow_le_pow_left₀ (abs_nonneg _) hr 2
  have hi2 := pow_le_pow_left₀ (abs_nonneg _) hi 2
  push_cast
  simp only [sq_abs] at hr2 hi2
  nlinarith

end QuantumAlg.MatrixBounds
