/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Effect
import all QuantumAlg.Core.Base.State.Density.Vector

/-!
# Observable comparison on a coherent subnormalized good component

Agreement is required on the whole rank-one good density, including all
cross terms between good basis labels. Certified effects supply contraction;
no unitary evolution is assumed for the program that produced an observable.
-/

namespace QuantumAlg.Effect

noncomputable section

variable {R : Register}

/-- The exact trace weight on a coherent subnormalized vector is its quadratic weight. -/
theorem weight_ofSubnormalizedVector (effect : Effect R) (vector : HilbertVector R)
    (bounded : ‖vector‖ ≤ 1) :
    effect.weight (DensityOperator.ofSubnormalizedVector vector bounded) =
      HilbertOperator.quadraticWeight effect.matrix vector := by
  unfold weight HilbertOperator.quadraticWeight
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    DensityOperator.ofSubnormalizedVector_matrix, PiLp.inner_apply,
    RCLike.inner_apply, starRingEnd_apply, HilbertOperator.applyVec_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr rfl
  intro other _
  ring

/-- Coherent good-density agreement preserves the four-times-omitted-norm event bound. -/
theorem weight_le_add_four_mul_omitted_norm (actual ideal : Effect R)
    (input : NormalizedVector R) (good : HilbertVector R) (bounded : ‖good‖ ≤ 1)
    (agrees : actual.weight (DensityOperator.ofSubnormalizedVector good bounded) =
      ideal.weight (DensityOperator.ofSubnormalizedVector good bounded)) :
    ideal.weight (DensityOperator.ofPure input) ≤ actual.weight (DensityOperator.ofPure input) +
      4 * ‖(input : HilbertVector R) - good‖ := by
  rw [weight_ofSubnormalizedVector, weight_ofSubnormalizedVector] at agrees
  rw [weight_ofPure, weight_ofPure]
  exact HilbertOperator.quadraticWeight_le_add_four_mul_norm_sub actual.matrix ideal.matrix
    actual.contractive ideal.contractive input good bounded agrees

end

end QuantumAlg.Effect
