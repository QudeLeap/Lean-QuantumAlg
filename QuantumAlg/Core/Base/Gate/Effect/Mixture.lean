/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Effect
import all QuantumAlg.Core.Base.State.Density.Spectral

/-!
# Extending pure-state event bounds to actual subnormalized mixtures

One bound uniform over normalized vectors extends to every positive density
with its original mass as a factor. Zero branches contribute zero. In later
execution applications, the effect must still be the pullback of the actual
program; this algebra alone supplies no independence or success assumption.
-/

namespace QuantumAlg.Effect

noncomputable section

variable {R : Register}

/-- A finite spectral sum gives the exact weight of this same observable. -/
theorem weight_eq_sum_spectral (effect : Effect R) (state : DensityOperator R) :
    effect.weight state = ∑ index, state.spectralMass index *
      effect.weight (DensityOperator.ofPure (state.spectralVector index)) := by
  unfold weight
  rw [state.matrix_eq_sum_spectral]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum, Complex.smul_re, smul_eq_mul]

/-- A uniform pure-input lower bound retains the mass of every actual mixed branch. -/
theorem mass_mul_le_weight_of_pure (effect : Effect R) (lower : ℝ)
    (bound : ∀ input : NormalizedVector R,
      lower ≤ effect.weight (DensityOperator.ofPure input)) (state : DensityOperator R) :
    state.mass * lower ≤ effect.weight state := by
  rw [weight_eq_sum_spectral, ← state.sum_spectralMass, Finset.sum_mul]
  exact Finset.sum_le_sum (fun index _ =>
    mul_le_mul_of_nonneg_left (bound (state.spectralVector index))
      (state.spectralMass_nonneg index))

/-- The corresponding upper bound also scales with the original branch mass. -/
theorem weight_le_mass_mul_of_pure (effect : Effect R) (upper : ℝ)
    (bound : ∀ input : NormalizedVector R,
      effect.weight (DensityOperator.ofPure input) ≤ upper) (state : DensityOperator R) :
    effect.weight state ≤ state.mass * upper := by
  rw [weight_eq_sum_spectral, ← state.sum_spectralMass, Finset.sum_mul]
  exact Finset.sum_le_sum (fun index _ =>
    mul_le_mul_of_nonneg_left (bound (state.spectralVector index))
      (state.spectralMass_nonneg index))

end

end QuantumAlg.Effect
