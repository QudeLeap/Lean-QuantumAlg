/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Effect

/-!
# Finite probability-weighted effects

A normalized nonnegative finite combination of positive contractions remains
a positive contraction. Its trace weight is the same combination of the
original weights against any subnormalized input density operator.
-/

open scoped ComplexOrder

namespace QuantumAlg.Effect

noncomputable section

variable {R : Register} {Index : Type} [Fintype Index]

private lemma weighted_positive (probability : Index → ℝ)
    (nonnegative : ∀ index, 0 ≤ probability index) (effects : Index → Effect R) :
    (∑ index, probability index • (effects index).matrix).PosSemidef := by
  classical
  refine Finset.induction_on (Finset.univ : Finset Index) ?_ ?_
  · simpa only [Finset.sum_empty] using (Matrix.PosSemidef.zero (n := R.Index) (R := ℂ))
  · intro index rest absent induction
    rw [Finset.sum_insert absent]
    exact ((effects index).positive.smul (nonnegative index)).add induction

private lemma weighted_contractive (probability : Index → ℝ)
    (nonnegative : ∀ index, 0 ≤ probability index) (total : ∑ index, probability index = 1)
    (effects : Index → Effect R) (vector : HilbertVector R) :
    ‖(∑ index, probability index • (effects index).matrix).applyVec vector‖ ≤ ‖vector‖ := by
  classical
  rw [HilbertOperator.sum_applyVec]
  calc
    ‖∑ index, (probability index • (effects index).matrix).applyVec vector‖ ≤
        ∑ index, ‖(probability index • (effects index).matrix).applyVec vector‖ :=
      norm_sum_le _ _
    _ ≤ ∑ index, probability index * ‖vector‖ := by
      apply Finset.sum_le_sum
      intro index _
      have action : (probability index • (effects index).matrix).applyVec vector =
          probability index • (effects index).matrix.applyVec vector := by
        unfold HilbertOperator.applyVec
        rw [Matrix.smul_mulVec]
        rfl
      rw [action, norm_smul, Real.norm_eq_abs, abs_of_nonneg (nonnegative index)]
      exact mul_le_mul_of_nonneg_left ((effects index).contractive vector) (nonnegative index)
    _ = ‖vector‖ := by rw [← Finset.sum_mul, total, one_mul]

/-- A finite normalized combination remains a certified positive contraction. -/
def weightedAverage (probability : Index → ℝ)
    (nonnegative : ∀ index, 0 ≤ probability index) (total : ∑ index, probability index = 1)
    (effects : Index → Effect R) : Effect R where
  matrix := ∑ index, probability index • (effects index).matrix
  positive := weighted_positive probability nonnegative effects
  contractive := weighted_contractive probability nonnegative total effects

/-- The weighted observable uses exactly the supplied finite probabilities and matrices. -/
lemma weightedAverage_matrix (probability : Index → ℝ)
    (nonnegative : ∀ index, 0 ≤ probability index) (total : ∑ index, probability index = 1)
    (effects : Index → Effect R) :
    (weightedAverage probability nonnegative total effects).matrix =
      ∑ index, probability index • (effects index).matrix := rfl

/-- Trace observation commutes with the normalized finite combination. -/
lemma weightedAverage_weight (probability : Index → ℝ)
    (nonnegative : ∀ index, 0 ≤ probability index) (total : ∑ index, probability index = 1)
    (effects : Index → Effect R) (state : DensityOperator R) :
    (weightedAverage probability nonnegative total effects).weight state =
      ∑ index, probability index * (effects index).weight state := by
  classical
  simp only [weight, weightedAverage_matrix, Matrix.sum_mul, Matrix.smul_mul,
    Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum, Complex.smul_re, smul_eq_mul]

end

end QuantumAlg.Effect
