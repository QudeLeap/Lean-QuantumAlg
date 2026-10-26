/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Util.CliffordT.Ring
import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Faithful complex interpretation of exact dyadic cyclotomic arithmetic
-/

@[expose] public section

namespace QuantumAlg.CliffordT

open QuadraticAlgebra

namespace DyadicSqrtTwo

/-- Evaluation of a real quadratic dyadic number at the positive square root. -/
noncomputable def toReal : DyadicSqrtTwo →+* ℝ where
  toFun z := (z.re : ℚ) + (z.im : ℚ) * Real.sqrt 2
  map_zero' := by simp
  map_one' := by simp
  map_add' z w := by simp; ring
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      Subring.coe_add, Subring.coe_mul, Subring.coe_zero,
      Rat.cast_add, Rat.cast_mul, Rat.cast_zero]
    change (z.re : ℚ) * (w.re : ℚ) + (2 : ℝ) * (z.im : ℚ) * (w.im : ℚ) +
      ((z.re : ℚ) * (w.im : ℚ) + (z.im : ℚ) * (w.re : ℚ) +
        0 * (z.im : ℚ) * (w.im : ℚ)) * Real.sqrt 2 = _
    ring_nf
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma coefficients_eq_zero (a b : ℚ)
    (h : (a : ℝ) + (b : ℝ) * Real.sqrt 2 = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    have hi := (irrational_sqrt_two.ratCast_mul hb).ratCast_add a
    exact hi.ne_rat 0 (by simpa using h)
  constructor
  · exact_mod_cast (show (a : ℝ) = 0 by simpa [hb] using h)
  · exact hb

lemma toReal_injective : Function.Injective toReal := by
  intro z w h
  have hz : toReal (z - w) = 0 := by rw [map_sub, h, sub_self]
  have hc := coefficients_eq_zero ((z - w).re : ℚ) ((z - w).im : ℚ) hz
  apply QuadraticAlgebra.ext
  · apply Subtype.ext
    exact sub_eq_zero.mp hc.1
  · apply Subtype.ext
    exact sub_eq_zero.mp hc.2

end DyadicSqrtTwo

namespace DOmega

/-- Exact arithmetic interpreted as a complex number. -/
noncomputable def toComplex : DOmega →+* ℂ where
  toFun z := ⟨DyadicSqrtTwo.toReal z.re, DyadicSqrtTwo.toReal z.im⟩
  map_zero' := by apply Complex.ext <;> simp
  map_one' := by apply Complex.ext <;> simp
  map_add' z w := by apply Complex.ext <;> simp
  map_mul' z w := by
    apply Complex.ext <;>
      simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, sub_eq_add_neg]

lemma toComplex_injective : Function.Injective toComplex := by
  intro z w h
  exact QuadraticAlgebra.ext
    (DyadicSqrtTwo.toReal_injective (congrArg Complex.re h))
    (DyadicSqrtTwo.toReal_injective (congrArg Complex.im h))

lemma toComplex_star (z : DOmega) : toComplex (star z) = star (toComplex z) := by
  apply Complex.ext <;> simp [toComplex]

lemma toComplex_sqrtTwo : toComplex sqrtTwo = (Real.sqrt 2 : ℂ) := by
  apply Complex.ext <;> simp [toComplex, DyadicSqrtTwo.toReal, sqrtTwo]

lemma toComplex_imaginary : toComplex imaginary = Complex.I := by
  apply Complex.ext <;> simp [toComplex, DyadicSqrtTwo.toReal, imaginary]

lemma toComplex_invSqrtTwo : toComplex invSqrtTwo = (Real.sqrt 2 : ℂ)⁻¹ := by
  have h : toComplex invSqrtTwo = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;>
      norm_num [toComplex, DyadicSqrtTwo.toReal, invSqrtTwo, half, div_eq_mul_inv,
        mul_comm]
  rw [h, Real.sqrt_div_self, Complex.ofReal_inv]

lemma toComplex_omega : toComplex DOmega.ω =
    (Real.sqrt 2 : ℂ)⁻¹ * (1 + Complex.I) := by
  rw [← toComplex_invSqrtTwo, ← toComplex_imaginary, ← map_one toComplex,
    ← map_add, ← map_mul]
  congr 1
  decide +kernel

end DOmega

end QuantumAlg.CliffordT
