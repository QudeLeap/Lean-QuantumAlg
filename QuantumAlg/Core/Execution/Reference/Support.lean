/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reference.Probability

/-!
# Full reference observations use only positive actual execution records

A zero-mass classical record carries the zero density operator. Consequently
weights that agree on positive complete execution records yield the same
reference observation, including off-diagonal reference coordinates.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

/-- A finite sum of actual weights commutes with the complete reference observation. -/
lemma referenceFiberSum_sum {C Index : Type} [Fintype C] [Fintype Index]
    {R Reference : Register} (state : ExecutionState C (Register.prod R Reference))
    (weight : Index → C → R.Index → ℂ) (left right : Reference.Index) :
    referenceFiberSum state (fun record basis => ∑ index, weight index record basis) left right =
      ∑ index, referenceFiberSum state (weight index) left right := by
  simp only [referenceFiberSum, Finset.sum_mul]
  calc
    _ = ∑ basis : R.Index, ∑ index : Index, ∑ record : C,
        weight index record basis * (state.block record).matrix (basis, left) (basis, right) := by
          apply Finset.sum_congr rfl
          intro basis _
          exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Agreement on actual positive records suffices for every complete reference fiber. -/
lemma referenceFiberSum_congr_on_positive {C : Type} [Fintype C] {R Reference : Register}
    (state : ExecutionState C (Register.prod R Reference))
    (first second : C → R.Index → ℂ)
    (matching : ∀ record, 0 < (state.block record).mass →
      ∀ basis, first record basis = second record basis)
    (left right : Reference.Index) :
    referenceFiberSum state first left right = referenceFiberSum state second left right := by
  unfold referenceFiberSum
  apply Finset.sum_congr rfl
  intro basis _
  apply Finset.sum_congr rfl
  intro record _
  by_cases positive : 0 < (state.block record).mass
  · rw [matching record positive basis]
  · have empty := block_eq_zero_of_mass_eq_zero state record
      (le_antisymm (le_of_not_gt positive) (state.block record).mass_nonneg)
    rw [empty]
    simp only [DensityOperator.zero, Matrix.zero_apply, mul_zero]

end

end QuantumAlg.ExecutionState
