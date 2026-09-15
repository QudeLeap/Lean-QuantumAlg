/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Periodic sine-square error bounds

This module transfers distance between phase representatives on the additive
unit circle to additive error in the decoded value `sin²(π phase)`.  The
signed-phase theorem makes explicit that the two opposite eigenphases used by
amplitude estimation decode to the same probability [Lin22,
appqpe.tex:209-228].
-/

section

namespace QuantumAlg

noncomputable section

/-- Decode a phase in turns to its sine-square probability. -/
def periodicSinSq (phase : ℝ) : ℝ :=
  Real.sin (Real.pi * phase) ^ 2

private theorem abs_sin_sq_sub_sin_sq_le (x y : ℝ) :
    |Real.sin x ^ 2 - Real.sin y ^ 2| ≤ |x - y| := by
  have hfactor :
      Real.sin x ^ 2 - Real.sin y ^ 2 =
        Real.sin (x + y) * Real.sin (x - y) := by
    have hx : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq x]
    have hy : Real.cos y ^ 2 = 1 - Real.sin y ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq y]
    rw [Real.sin_add, Real.sin_sub]
    ring_nf
    rw [hx, hy]
    ring
  rw [hfactor, abs_mul]
  calc
    |Real.sin (x + y)| * |Real.sin (x - y)| ≤
        1 * |Real.sin (x - y)| :=
      mul_le_mul_of_nonneg_right (Real.abs_sin_le_one (x + y))
        (abs_nonneg _)
    _ = |Real.sin (x - y)| := one_mul _
    _ ≤ |x - y| := Real.abs_sin_le_abs

/-- Opposite phase representatives decode to the same probability. -/
theorem periodicSinSq_neg (phase : ℝ) :
    periodicSinSq (-phase) = periodicSinSq phase := by
  simp [periodicSinSq]

/-- Shifting a phase representative by an integer does not change its decoded
probability. -/
theorem periodicSinSq_add_int (phase : ℝ) (z : ℤ) :
    periodicSinSq (phase + (z : ℝ)) = periodicSinSq phase := by
  rw [periodicSinSq, periodicSinSq]
  rw [show Real.pi * (phase + (z : ℝ)) =
      Real.pi * phase + (z : ℝ) * Real.pi by ring]
  rw [Real.sin_add_int_mul_pi]
  calc
    (((-1 : ℝ) ^ z) * Real.sin (Real.pi * phase)) ^ 2 =
        |((-1 : ℝ) ^ z) * Real.sin (Real.pi * phase)| ^ 2 :=
      (sq_abs _).symm
    _ = (1 * |Real.sin (Real.pi * phase)|) ^ 2 := by
      rw [abs_mul, abs_neg_one_zpow]
    _ = |Real.sin (Real.pi * phase)| ^ 2 := by rw [one_mul]
    _ = Real.sin (Real.pi * phase) ^ 2 := sq_abs _

/-- The decoded sine-square probability is `π`-Lipschitz with respect to
periodic phase distance on `UnitAddCircle`. -/
theorem periodicSinSq_sub_le_circleNorm (x y : ℝ) :
    |periodicSinSq x - periodicSinSq y| ≤
      Real.pi * ‖((x - y : ℝ) : UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq]
  let z : ℤ := round (x - y)
  change |periodicSinSq x - periodicSinSq y| ≤
    Real.pi * |(x - y) - (z : ℝ)|
  calc
    |periodicSinSq x - periodicSinSq y| =
        |periodicSinSq x - periodicSinSq (y + (z : ℝ))| := by
      rw [periodicSinSq_add_int]
    _ ≤ |Real.pi * x - Real.pi * (y + (z : ℝ))| :=
      abs_sin_sq_sub_sin_sq_le _ _
    _ = |Real.pi * ((x - y) - (z : ℝ))| := by
      congr 1
      ring
    _ = Real.pi * |(x - y) - (z : ℝ)| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]

/-- An estimate close to either of the two opposite eigenphases decodes to the
same sine-square probability, with additive error controlled by the periodic
phase distance. -/
theorem periodicSinSq_error_of_signed_phase
    (phase estimate eps : ℝ)
    (hphase :
      ‖((estimate - phase : ℝ) : UnitAddCircle)‖ ≤ eps ∨
        ‖((estimate + phase : ℝ) : UnitAddCircle)‖ ≤ eps) :
    |periodicSinSq estimate - periodicSinSq phase| ≤ Real.pi * eps := by
  rcases hphase with hpositive | hnegative
  · exact (periodicSinSq_sub_le_circleNorm estimate phase).trans
      (mul_le_mul_of_nonneg_left hpositive Real.pi_pos.le)
  · calc
      |periodicSinSq estimate - periodicSinSq phase| =
          |periodicSinSq estimate - periodicSinSq (-phase)| := by
        rw [periodicSinSq_neg]
      _ ≤ Real.pi * ‖((estimate - (-phase) : ℝ) : UnitAddCircle)‖ :=
        periodicSinSq_sub_le_circleNorm estimate (-phase)
      _ ≤ Real.pi * eps := by
        apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
        simpa [sub_neg_eq_add] using hnegative

end

end QuantumAlg

end
