/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Effect.Support

/-!
# Complete coherent weights from matching observable columns

Equality of every matrix entry between two finite families of basis labels
preserves the weight of their complete coherent sums with the same complex
amplitudes. All cross terms are retained. Injectivity of the label families
is unnecessary: repeated labels still contribute their actual interfering
amplitudes. Both supplied sums keep their original subnormalization.
-/

namespace QuantumAlg.Effect

noncomputable section

private theorem operator_finite_sum {R : Register} (operator : HilbertOperator R)
    {Index : Type} (indices : Finset Index) (vectors : Index → HilbertVector R) :
    operator.applyVec (∑ index ∈ indices, vectors index) =
      ∑ index ∈ indices, operator.applyVec (vectors index) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      apply WithLp.ofLp_injective
      funext label
      simp [HilbertOperator.applyVec_apply]
  | @insert index indices absent induction =>
      simp only [Finset.sum_insert absent, HilbertOperator.applyVec_add, induction]

private theorem inner_ket_column {R : Register} (operator : HilbertOperator R)
    (left right : R.Index) :
    inner ℂ (NormalizedVector.ket left : HilbertVector R)
      (operator.applyVec (NormalizedVector.ket right : HilbertVector R)) =
        operator left right := by
  classical
  simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply,
    NormalizedVector.ket_apply, HilbertOperator.applyVec_ket]
  simp

private theorem coherent_inner_columns {R : Register} (operator : HilbertOperator R)
    {Index : Type} (indices : Finset Index) (labels : Index → R.Index)
    (amplitude : Index → ℂ) :
    inner ℂ (∑ index ∈ indices,
      amplitude index • (NormalizedVector.ket (labels index) : HilbertVector R))
      (operator.applyVec (∑ index ∈ indices,
        amplitude index • (NormalizedVector.ket (labels index) : HilbertVector R))) =
      ∑ left ∈ indices, ∑ right ∈ indices,
        star (amplitude left) * operator (labels left) (labels right) * amplitude right := by
  rw [operator_finite_sum]
  simp only [sum_inner, inner_sum, HilbertOperator.applyVec_smul,
    inner_smul_left, inner_smul_right, Finset.mul_sum, starRingEnd_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  rw [inner_ket_column]
  ring

/-- Matching every selected matrix entry preserves the entire coherent subnormalized weight. -/
theorem weight_eq_of_coherent_columns {R S : Register} {Index : Type}
    (indices : Finset Index) (amplitude : Index → ℂ)
    (leftLabel : Index → R.Index) (rightLabel : Index → S.Index)
    (leftEffect : Effect R) (rightEffect : Effect S)
    (leftBound : ‖∑ index ∈ indices,
      amplitude index • (NormalizedVector.ket (leftLabel index) : HilbertVector R)‖ ≤ 1)
    (rightBound : ‖∑ index ∈ indices,
      amplitude index • (NormalizedVector.ket (rightLabel index) : HilbertVector S)‖ ≤ 1)
    (columns : ∀ left ∈ indices, ∀ right ∈ indices,
      leftEffect.matrix (leftLabel left) (leftLabel right) =
        rightEffect.matrix (rightLabel left) (rightLabel right)) :
    leftEffect.weight (DensityOperator.ofSubnormalizedVector
      (∑ index ∈ indices,
        amplitude index • (NormalizedVector.ket (leftLabel index) : HilbertVector R))
      leftBound) =
      rightEffect.weight (DensityOperator.ofSubnormalizedVector
        (∑ index ∈ indices,
          amplitude index • (NormalizedVector.ket (rightLabel index) : HilbertVector S))
        rightBound) := by
  rw [weight_ofSubnormalizedVector, weight_ofSubnormalizedVector]
  unfold HilbertOperator.quadraticWeight
  rw [coherent_inner_columns, coherent_inner_columns]
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro left leftMember
  apply Finset.sum_congr rfl
  intro right rightMember
  rw [columns left leftMember right rightMember]

end

end QuantumAlg.Effect
