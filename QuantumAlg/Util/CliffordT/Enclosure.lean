/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Util.CliffordT.Embedding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Rational enclosures of dyadic quadratic coefficients

The interval endpoints for the positive square root of two are certified by
rational square comparisons. Multiplication respects either sign of the exact
quadratic coefficient.
-/

@[expose] public section

namespace QuantumAlg.CliffordT.DyadicSqrtTwo

/-- Rational lower bound on the positive square root of two. -/
def sqrtLo : ℚ := 1.41421356237309504880

/-- Rational upper bound on the positive square root of two. -/
def sqrtHi : ℚ := 1.41421356237309504881

lemma sqrtLo_le_sqrt_two : (sqrtLo : ℝ) ≤ Real.sqrt 2 := by
  apply (Real.le_sqrt (by norm_num [sqrtLo]) (by norm_num)).mpr
  norm_num [sqrtLo]

lemma sqrt_two_le_sqrtHi : Real.sqrt 2 ≤ (sqrtHi : ℝ) := by
  apply (Real.sqrt_le_iff).mpr
  norm_num [sqrtHi]

/-- Lower rational endpoint for the real interpretation of a quadratic coefficient. -/
def lower (z : DyadicSqrtTwo) : ℚ :=
  (z.re : ℚ) + min ((z.im : ℚ) * sqrtLo) ((z.im : ℚ) * sqrtHi)

/-- Upper rational endpoint for the real interpretation of a quadratic coefficient. -/
def upper (z : DyadicSqrtTwo) : ℚ :=
  (z.re : ℚ) + max ((z.im : ℚ) * sqrtLo) ((z.im : ℚ) * sqrtHi)

lemma lower_le_toReal (z : DyadicSqrtTwo) : (lower z : ℝ) ≤ toReal z := by
  simp only [lower, Rat.cast_add, Rat.cast_min, Rat.cast_mul, toReal, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk]
  refine add_le_add le_rfl ?_
  by_cases hb : (0 : ℝ) ≤ (z.im : ℚ)
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left sqrtLo_le_sqrt_two hb)
  · exact (min_le_right _ _).trans
      (mul_le_mul_of_nonpos_left sqrt_two_le_sqrtHi (le_of_not_ge hb))

lemma toReal_le_upper (z : DyadicSqrtTwo) : toReal z ≤ (upper z : ℝ) := by
  simp only [upper, Rat.cast_add, Rat.cast_max, Rat.cast_mul, toReal, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk]
  refine add_le_add le_rfl ?_
  by_cases hb : (0 : ℝ) ≤ (z.im : ℚ)
  · exact (mul_le_mul_of_nonneg_left sqrt_two_le_sqrtHi hb).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_left sqrtLo_le_sqrt_two (le_of_not_ge hb)).trans
      (le_max_left _ _)

end QuantumAlg.CliffordT.DyadicSqrtTwo
