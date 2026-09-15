/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Base.Gate.QuadraticStability

/-!
# Finite positive contractive effects

An effect is a positive matrix with its vector contraction certified on the
same finite register. Its weight is the trace pairing with an actual density
matrix. This carrier introduces no execution instruction or channel.
-/

open scoped ComplexOrder

namespace QuantumAlg

/-- A positive observable bounded by vector contraction on its full register. -/
structure Effect (R : Register) where
  /-- Matrix of the observable. -/
  matrix : HilbertOperator R
  /-- Positivity includes Hermitian symmetry. -/
  positive : matrix.PosSemidef
  /-- Applying this same matrix cannot increase any vector norm. -/
  contractive : ∀ vector : HilbertVector R, ‖matrix.applyVec vector‖ ≤ ‖vector‖

namespace Effect

noncomputable section

variable {R : Register}

/-- Trace weight against the same subnormalized density operator. -/
def weight (effect : Effect R) (state : DensityOperator R) : ℝ :=
  (effect.matrix * state.matrix).trace.re

/-- On a pure input, the density trace pairing is its coherent quadratic form. -/
theorem weight_ofPure (effect : Effect R) (input : NormalizedVector R) :
    effect.weight (DensityOperator.ofPure input) =
      HilbertOperator.quadraticWeight effect.matrix input := by
  unfold weight HilbertOperator.quadraticWeight
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, DensityOperator.ofPure_matrix,
    PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply,
    HilbertOperator.applyVec_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr rfl
  intro other _
  ring

/-- The certain effect observes all retained probability mass. -/
def one (R : Register) : Effect R where
  matrix := 1
  positive := Matrix.PosSemidef.one
  contractive vector := by simp

/-- The impossible effect has zero weight. -/
def zero (R : Register) : Effect R where
  matrix := 0
  positive := Matrix.PosSemidef.zero
  contractive vector := by
    have vanish : HilbertOperator.applyVec (0 : HilbertOperator R) vector = 0 := by
      ext index
      simp [HilbertOperator.applyVec_apply]
    rw [vanish, norm_zero]
    exact norm_nonneg _

@[simp] theorem weight_one (state : DensityOperator R) :
    (one R).weight state = state.mass := by simp [weight, one, DensityOperator.mass]

@[simp] theorem weight_zero (state : DensityOperator R) :
    (zero R).weight state = 0 := by simp [weight, zero]

end

end Effect

end QuantumAlg
