/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Effect

/-!
# Uniform averages of finite effects

A nonempty finite average of positive contractive effects is again a positive
contractive effect on the same register. Its weight is the exact average of
the original trace weights against any subnormalized density matrix.
-/

open scoped ComplexOrder

namespace QuantumAlg.Effect

noncomputable section

variable {R : Register} {Index : Type} [Fintype Index]

private lemma sum_positive (effects : Index → Effect R) :
    (∑ index, (effects index).matrix).PosSemidef := by
  classical
  refine Finset.induction_on (Finset.univ : Finset Index) ?_ ?_
  · simpa only [Finset.sum_empty] using (Matrix.PosSemidef.zero (n := R.Index) (R := ℂ))
  · intro index rest absent induction
    rw [Finset.sum_insert absent]
    exact (effects index).positive.add induction

private lemma real_smul_applyVec (scalar : ℝ) (matrix : HilbertOperator R)
    (vector : HilbertVector R) :
    (scalar • matrix).applyVec vector = scalar • matrix.applyVec vector := by
  unfold HilbertOperator.applyVec
  rw [Matrix.smul_mulVec]
  rfl

variable [Nonempty Index]

private lemma average_contractive (effects : Index → Effect R) (vector : HilbertVector R) :
    ‖((Fintype.card Index : ℝ)⁻¹ • ∑ index, (effects index).matrix).applyVec vector‖ ≤
      ‖vector‖ := by
  classical
  have nonnegative : 0 ≤ (Fintype.card Index : ℝ)⁻¹ := by positivity
  have nonzero : (Fintype.card Index : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [real_smul_applyVec, norm_smul, Real.norm_eq_abs, abs_of_nonneg nonnegative,
    HilbertOperator.sum_applyVec]
  calc
    (Fintype.card Index : ℝ)⁻¹ * ‖∑ index, (effects index).matrix.applyVec vector‖ ≤
        (Fintype.card Index : ℝ)⁻¹ * ∑ index, ‖(effects index).matrix.applyVec vector‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) nonnegative
    _ ≤ (Fintype.card Index : ℝ)⁻¹ * ∑ _index : Index, ‖vector‖ :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun index _ => (effects index).contractive vector)) nonnegative
    _ = ‖vector‖ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ nonzero, one_mul]

/-- The actual uniform finite average remains a positive contraction on the same register. -/
def uniformAverage (effects : Index → Effect R) : Effect R where
  matrix := (Fintype.card Index : ℝ)⁻¹ • ∑ index, (effects index).matrix
  positive := (sum_positive effects).smul (by positivity)
  contractive := average_contractive effects

/-- The average effect uses exactly the original matrices and real uniform sampling weight. -/
lemma uniformAverage_matrix (effects : Index → Effect R) :
    (uniformAverage effects).matrix =
      (Fintype.card Index : ℝ)⁻¹ • ∑ index, (effects index).matrix := rfl

/-- Trace weight commutes with the exact finite uniform average for every input density. -/
lemma uniformAverage_weight (effects : Index → Effect R) (state : DensityOperator R) :
    (uniformAverage effects).weight state =
      (Fintype.card Index : ℝ)⁻¹ * ∑ index, (effects index).weight state := by
  classical
  simp only [weight, uniformAverage_matrix, Matrix.smul_mul, Matrix.sum_mul,
    Matrix.trace_smul, Matrix.trace_sum, Complex.smul_re, smul_eq_mul]
  congr 1
  exact map_sum Complex.reAddGroupHom _ _

end

end QuantumAlg.Effect
