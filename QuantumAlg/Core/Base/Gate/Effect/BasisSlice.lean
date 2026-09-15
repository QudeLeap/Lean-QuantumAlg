/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Effect.Embedding
import all QuantumAlg.Core.Base.Gate.Effect.Mixture
import all QuantumAlg.Core.Base.State.Density.ReferenceBlock

/-!
# Exact event compression on a genuinely fixed local basis

A full joint density supported on one local ket has precisely the event
weight of its actual reference block and the compressed original observable.
Uniform pure-reference bounds therefore apply to mixed conditional blocks
with their unchanged mass. The ket support remains a premise to be proved by
the actual reset execution.
-/

namespace QuantumAlg.Effect

noncomputable section

variable {R Reference : Register}

/-- Restrict the original full observable to a named local ket and its complete reference. -/
def basisSliceEffect (effect : Effect (R.prod Reference)) (label : R.Index) : Effect Reference :=
  compress (fun reference => (label, reference)) (fun _ _ equality =>
    congrArg Prod.snd equality) effect

/-- A fixed local ket has exactly the compressed effect's actual conditional reference weight. -/
theorem weight_basisSlice_of_factor (effect : Effect (R.prod Reference))
    (state : DensityOperator (R.prod Reference)) (label : R.Index)
    (factor : ∀ left right : R.Index, ∀ refLeft refRight : Reference.Index,
      state.matrix (left, refLeft) (right, refRight) =
        NormalizedVector.ket label left * state.matrix (label, refLeft) (label, refRight) *
          star (NormalizedVector.ket label right)) :
    effect.weight state = (effect.basisSliceEffect label).weight (state.basisSlice label) := by
  classical
  have entry (left right : R.Index) (refLeft refRight : Reference.Index) :
      state.matrix (left, refLeft) (right, refRight) =
        if left = label ∧ right = label then
          (state.basisSlice label).matrix refLeft refRight else 0 := by
    rw [factor left right refLeft refRight]
    by_cases sameLeft : left = label <;> by_cases sameRight : right = label <;>
      simp [NormalizedVector.ket_apply, sameLeft, sameRight, DensityOperator.basisSlice_matrix]
  unfold weight
  apply congrArg Complex.re
  change (∑ row : R.Index × Reference.Index, ∑ column : R.Index × Reference.Index,
    effect.matrix row column * state.matrix column row) =
      ∑ row : Reference.Index, ∑ column : Reference.Index,
        effect.matrix (label, row) (label, column) *
          (state.basisSlice label).matrix column row
  simp only [Fintype.sum_prod_type]
  simp only [entry, mul_ite, mul_zero]
  simp [ite_and]

/-- A uniform bound for pure references applies to the full actual mixed ket-supported block. -/
theorem mass_mul_le_weight_of_basis_factor (effect : Effect (R.prod Reference))
    (state : DensityOperator (R.prod Reference)) (label : R.Index) (lower : ℝ)
    (factor : ∀ left right : R.Index, ∀ refLeft refRight : Reference.Index,
      state.matrix (left, refLeft) (right, refRight) =
        NormalizedVector.ket label left * state.matrix (label, refLeft) (label, refRight) *
          star (NormalizedVector.ket label right))
    (bound : ∀ input : NormalizedVector Reference,
      lower ≤ (effect.basisSliceEffect label).weight (DensityOperator.ofPure input)) :
    state.mass * lower ≤ effect.weight state := by
  rw [weight_basisSlice_of_factor effect state label factor,
    ← state.basisSlice_mass_of_factor label factor]
  exact mass_mul_le_weight_of_pure _ lower bound _

end

end QuantumAlg.Effect
