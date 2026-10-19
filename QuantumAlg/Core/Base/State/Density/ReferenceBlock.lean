/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.State.Density

/-!
# The original reference block at a fixed local basis value

Taking a principal matrix block keeps positivity and never increases mass.
When the full joint state is supported on that local ket, the block retains
exactly the full branch mass. No division by a probability is performed.
-/

namespace QuantumAlg.DensityOperator

noncomputable section

open scoped ComplexOrder

variable {R Reference : Register}

private lemma basisSlice_trace_le (state : DensityOperator (R.prod Reference))
    (label : R.Index) :
    (state.matrix.submatrix (fun index => (label, index))
      (fun index => (label, index))).trace.re ≤ state.mass := by
  change (∑ index : Reference.Index, state.matrix (label, index) (label, index)).re ≤
    (∑ index : R.Index × Reference.Index, state.matrix index index).re
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [Complex.re_sum]
  have nonnegative (basis : R.Index) :
      0 ≤ (∑ reference : Reference.Index,
        state.matrix (basis, reference) (basis, reference)).re :=
    (Complex.nonneg_iff.mp (Finset.sum_nonneg fun reference _ =>
      state.positive.diag_nonneg (i := (basis, reference)))).1
  exact Finset.single_le_sum (fun basis _ => nonnegative basis) (Finset.mem_univ label)

/-- The same conditional reference matrix, with its actual subnormalized mass. -/
def basisSlice (state : DensityOperator (R.prod Reference)) (label : R.Index) :
    DensityOperator Reference where
  matrix := state.matrix.submatrix (fun index => (label, index)) (fun index => (label, index))
  positive := state.positive.submatrix (fun index => (label, index))
  trace_le_one := (basisSlice_trace_le state label).trans state.trace_le_one

/-- Slicing preserves every complex reference entry at that actual local basis. -/
lemma basisSlice_matrix (state : DensityOperator (R.prod Reference)) (label : R.Index)
    (left right : Reference.Index) :
    (state.basisSlice label).matrix left right = state.matrix (label, left) (label, right) := rfl

/-- A principal reference block cannot contain more probability than the whole input. -/
lemma basisSlice_mass_le (state : DensityOperator (R.prod Reference)) (label : R.Index) :
    (state.basisSlice label).mass ≤ state.mass := basisSlice_trace_le state label

/-- Full local ket support keeps the complete mass in the same reference block. -/
lemma basisSlice_mass_of_factor (state : DensityOperator (R.prod Reference)) (label : R.Index)
    (factor : ∀ left right : R.Index, ∀ refLeft refRight : Reference.Index,
      state.matrix (left, refLeft) (right, refRight) =
        NormalizedVector.ket label left * state.matrix (label, refLeft) (label, refRight) *
          star (NormalizedVector.ket label right)) :
    (state.basisSlice label).mass = state.mass := by
  unfold mass
  congr 1
  change (∑ index : Reference.Index, state.matrix (label, index) (label, index)) =
    ∑ index : R.Index × Reference.Index, state.matrix index index
  rw [Fintype.sum_prod_type]
  have diagonal (basis : R.Index) (reference : Reference.Index) :
      state.matrix (basis, reference) (basis, reference) =
        if basis = label then state.matrix (label, reference) (label, reference) else 0 := by
    rw [factor basis basis reference reference]
    by_cases same : basis = label <;> simp [NormalizedVector.ket_apply, same]
  classical
  calc
    _ = ∑ basis : R.Index, ∑ reference : Reference.Index,
        if basis = label then state.matrix (label, reference) (label, reference) else 0 := by
      simp
    _ = _ := Finset.sum_congr rfl (fun basis _ =>
      Finset.sum_congr rfl (fun reference _ => (diagonal basis reference).symm))

end

end QuantumAlg.DensityOperator
