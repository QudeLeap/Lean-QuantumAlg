/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Effect.BasisSlice

/-!
# Pure inputs in the same fixed-basis observable coordinates

An explicit ket-times-reference amplitude equation identifies the original
full pure input with the compressed reference observation. This is an exact
matrix-weight identity; it creates no state preparation or alternate input.
-/

namespace QuantumAlg.Effect

noncomputable section

variable {R Reference : Register}

/-- The original ket-times-reference input has the compressed reference's exact event weight. -/
theorem basisSliceEffect_weight_of_pure (effect : Effect (R.prod Reference)) (label : R.Index)
    (reference : NormalizedVector Reference) (input : NormalizedVector (R.prod Reference))
    (represented : ∀ left : R.Index, ∀ right : Reference.Index,
      input (left, right) = NormalizedVector.ket (R := R) label left * reference right) :
    (effect.basisSliceEffect label).weight (DensityOperator.ofPure reference) =
      effect.weight (DensityOperator.ofPure input) := by
  have factor (left right : R.Index) (refLeft refRight : Reference.Index) :
      (DensityOperator.ofPure input).matrix (left, refLeft) (right, refRight) =
        NormalizedVector.ket (R := R) label left *
          (DensityOperator.ofPure input).matrix (label, refLeft) (label, refRight) *
            star (NormalizedVector.ket (R := R) label right) := by
    simp only [DensityOperator.ofPure_matrix, represented, NormalizedVector.ket_apply]
    by_cases sameLeft : left = label <;> by_cases sameRight : right = label <;>
      simp [sameLeft, sameRight]
  have sliced : (DensityOperator.ofPure input).basisSlice label =
      DensityOperator.ofPure reference := by
    apply DensityOperator.ext
    ext left right
    simp only [DensityOperator.basisSlice_matrix, DensityOperator.ofPure_matrix,
      represented, NormalizedVector.ket_apply, if_true, one_mul]
  rw [weight_basisSlice_of_factor (R := R) (Reference := Reference) effect
    (DensityOperator.ofPure input) label factor, sliced]

end

end QuantumAlg.Effect
