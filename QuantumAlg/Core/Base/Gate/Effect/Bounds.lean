/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Effect.Mixture

/-!
# Event weights lie between zero and the actual retained mass

Positivity and vector contraction bound pure observations. Their exact
spectral extension gives the same bounds for arbitrary subnormalized density
operators, including zero branches.
-/

namespace QuantumAlg.Effect

noncomputable section

open scoped ComplexOrder

variable {R : Register}

/-- A certified positive observable has nonnegative weight on every represented density. -/
lemma weight_nonneg (effect : Effect R) (state : DensityOperator R) :
    0 ≤ effect.weight state := by
  have pure (input : NormalizedVector R) :
      0 ≤ effect.weight (DensityOperator.ofPure input) := by
    rw [weight_ofPure, HilbertOperator.quadraticWeight,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    exact effect.positive.re_dotProduct_nonneg _
  simpa only [mul_zero] using mass_mul_le_weight_of_pure effect 0 pure state

/-- No certified event carries more weight than the same input branch's actual mass. -/
lemma weight_le_mass (effect : Effect R) (state : DensityOperator R) :
    effect.weight state ≤ state.mass := by
  have pure (input : NormalizedVector R) :
      effect.weight (DensityOperator.ofPure input) ≤ 1 := by
    rw [weight_ofPure]
    unfold HilbertOperator.quadraticWeight
    refine (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    rw [input.norm_eq_one, one_mul]
    exact (effect.contractive input).trans_eq input.norm_eq_one
  simpa only [mul_one] using weight_le_mass_mul_of_pure effect 1 pure state

end

end QuantumAlg.Effect
