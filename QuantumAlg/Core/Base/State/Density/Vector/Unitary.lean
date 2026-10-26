/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.State.Density.Vector

/-!
# Unitary evolution of the same coherent subnormalized vector

The rank-one identity retains the vector's original mass, including zero.
Its matrix proof is the same outer-product calculation used by ofPure_apply;
no normalization or conditioning is introduced.
-/

namespace QuantumAlg.DensityOperator

noncomputable section

/-- Unitary density evolution preserves the exact original raw-vector representation. -/
lemma ofSubnormalizedVector_apply {R : Register} (operator : UnitaryOperator R)
    (vector : HilbertVector R) (bounded : ‖vector‖ ≤ 1) :
    ofSubnormalizedVector (operator.applyVec vector)
        (by rw [operator.norm_applyVec]; exact bounded) =
      applyUnitary operator (ofSubnormalizedVector vector bounded) := by
  apply ext
  ext row column
  change (∑ left, operator row left * vector left) *
      star (∑ right, operator column right * vector right) =
    ∑ right, (∑ left, operator row left * (vector left * star (vector right))) *
      star (operator column right)
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _
  apply Finset.sum_congr rfl
  intro left _
  ring

end

end QuantumAlg.DensityOperator
