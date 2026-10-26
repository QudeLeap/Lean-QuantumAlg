/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Target
public import QuantumAlg.Util.CliffordT.Enclosure
public import QuantumAlg.Util.CliffordT.Matrix
public import QuantumAlg.Util.Matrix.TwoByTwoNorm

/-!
# Rational squared Frobenius error bounds

All numerical bounds are rational. Squaring avoids computing square roots in
the certificate checker; nonnegative tolerances are checked separately.
-/

@[expose] public section

namespace QuantumAlg.CliffordT.Checker

open scoped Matrix.Norms.L2Operator

/-- A rational rectangle in the complex plane. -/
structure Rectangle where
  /-- Lower real endpoint. -/
  reLo : ℚ
  /-- Upper real endpoint. -/
  reHi : ℚ
  /-- Lower imaginary endpoint. -/
  imLo : ℚ
  /-- Upper imaginary endpoint. -/
  imHi : ℚ

/-- Target-entry rectangle with the negative phase in the first diagonal entry. -/
def targetRectangle (j : ℕ) (i k : Fin 2) : Rectangle :=
  if i = k then
    ⟨cosLower j, cosUpper j,
      if i = 0 then -sinUpper j else sinLower j,
      if i = 0 then -sinLower j else sinUpper j⟩
  else ⟨0, 0, 0, 0⟩

lemma targetRectangle_sound (j : ℕ) (i k : Fin 2) :
    ((targetRectangle j i k).reLo : ℝ) ≤ (targetMatrix j i k).re ∧
    (targetMatrix j i k).re ≤ ((targetRectangle j i k).reHi : ℝ) ∧
    ((targetRectangle j i k).imLo : ℝ) ≤ (targetMatrix j i k).im ∧
    (targetMatrix j i k).im ≤ ((targetRectangle j i k).imHi : ℝ) := by
  have hc := target_cos_bounds j
  have hs := target_sin_bounds j
  by_cases hik : i = k
  · subst k
    by_cases hi : i = 0
    · simpa [targetRectangle, targetMatrix, hi, Complex.mul_re, Complex.mul_im,
        -Complex.ofReal_cos, -Complex.ofReal_sin] using
        And.intro hc.1 (And.intro hc.2 (And.intro (neg_le_neg hs.2) (neg_le_neg hs.1)))
    · simpa [targetRectangle, targetMatrix, hi, Complex.mul_re, Complex.mul_im,
        -Complex.ofReal_cos, -Complex.ofReal_sin] using
        And.intro hc.1 (And.intro hc.2 hs)
  · simp [targetRectangle, targetMatrix, hik]

/-- Squared coordinate error bound between an exact ring entry and a rectangle. -/
def entryErrorSq (z : DOmega) (r : Rectangle) : ℚ :=
  (max |DyadicSqrtTwo.lower z.re - r.reHi| |DyadicSqrtTwo.upper z.re - r.reLo|) ^ 2 +
  (max |DyadicSqrtTwo.lower z.im - r.imHi| |DyadicSqrtTwo.upper z.im - r.imLo|) ^ 2

lemma entryErrorSq_sound (z : DOmega) (b : ℂ) (r : Rectangle)
    (hr : (r.reLo : ℝ) ≤ b.re) (hr' : b.re ≤ (r.reHi : ℝ))
    (hi : (r.imLo : ℝ) ≤ b.im) (hi' : b.im ≤ (r.imHi : ℝ)) :
    ‖DOmega.toComplex z - b‖ ^ 2 ≤ (entryErrorSq z r : ℝ) := by
  have h := MatrixBounds.norm_sub_le_interval (DOmega.toComplex z) b.re b.im
    (DyadicSqrtTwo.lower z.re) (DyadicSqrtTwo.upper z.re)
    (DyadicSqrtTwo.lower z.im) (DyadicSqrtTwo.upper z.im)
    r.reLo r.reHi r.imLo r.imHi
    (DyadicSqrtTwo.lower_le_toReal z.re) (DyadicSqrtTwo.toReal_le_upper z.re)
    (DyadicSqrtTwo.lower_le_toReal z.im) (DyadicSqrtTwo.toReal_le_upper z.im)
    hr hr' hi hi'
  have hb : (b.re : ℂ) + Complex.I * b.im = b := by
    rw [mul_comm]
    exact Complex.re_add_im b
  rw [hb] at h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [Real.sq_sqrt (by positivity)] at hsq
  simpa only [entryErrorSq, Rat.cast_add, Rat.cast_pow] using hsq

/-- Rational upper bound on the squared Frobenius error of the exact matrix. -/
def matrixErrorSq (A : Mat2) (j : ℕ) : ℚ :=
  ∑ i, ∑ k, entryErrorSq (A i k) (targetRectangle j i k)

lemma matrixErrorSq_nonneg (A : Mat2) (j : ℕ) : 0 ≤ matrixErrorSq A j := by
  unfold matrixErrorSq entryErrorSq
  positivity

lemma matrixErrorSq_sound (A : Mat2) (j : ℕ) :
    ‖toComplexMat A - targetMatrix j‖ ≤ Real.sqrt (matrixErrorSq A j) := by
  apply (MatrixBounds.opNorm_le_frobenius _).trans
  apply Real.sqrt_le_sqrt
  simp only [matrixErrorSq, Rat.cast_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro k _
  have h := targetRectangle_sound j i k
  exact entryErrorSq_sound (A i k) (targetMatrix j i k) (targetRectangle j i k)
    h.1 h.2.1 h.2.2.1 h.2.2.2

end QuantumAlg.CliffordT.Checker
