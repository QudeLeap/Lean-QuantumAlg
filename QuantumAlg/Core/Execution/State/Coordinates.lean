/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reindex

/-!
# Complete block coordinates under exact classical and quantum relabeling

A bijection of classical labels retains each complete density block.
Changing quantum basis coordinates commutes with the existing finite
classical block sum. These are identities of the current state carrier,
with no instruction, measurement family or additional execution mechanism
[dW19, qcnotes.tex:5381,5394,5409].
-/

namespace QuantumAlg.ExecutionState

noncomputable section

variable {C D : Type} [Fintype C] [Fintype D] [DecidableEq D]
  {R S : Register}

/-- A bijective label change retains precisely the original complete density block. -/
lemma coordinate_mapClassical_block (state : ExecutionState C R) (labels : C ≃ D)
    (value : D) :
    (state.mapClassical labels).block value = state.block (labels.symm value) := by
  classical
  apply DensityOperator.ext
  change (∑ input, if labels input = value then (state.block input).matrix else 0) = _
  simp only [← Equiv.eq_symm_apply]
  simp

/-- Existing quantum coordinate changes commute with arbitrary actual classical block sums. -/
lemma coordinate_reindex_mapClassical (state : ExecutionState C R)
    (basis : R.Index ≃ S.Index) (labels : C → D) :
    (state.reindex basis).mapClassical labels = (state.mapClassical labels).reindex basis := by
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  simp only [ExecutionState.reindex, ExecutionState.mapClassical, DensityOperator.reindex,
    Matrix.submatrix_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro original _
  split <;> rfl

/-- A forward and inverse classical coordinate change restore the complete initial state. -/
lemma coordinate_mapClassical_inverse [DecidableEq C]
    (state : ExecutionState C R) (labels : C ≃ D) :
    (state.mapClassical labels).mapClassical labels.symm = state := by
  apply ExecutionState.ext
  intro value
  rw [coordinate_mapClassical_block, coordinate_mapClassical_block]
  simp only [Equiv.symm_symm, Equiv.symm_apply_apply]

/-- A forward and inverse basis correspondence restore every classical and quantum entry. -/
lemma coordinate_reindex_inverse (state : ExecutionState C R) (basis : R.Index ≃ S.Index) :
    (state.reindex basis).reindex basis.symm = state := by
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  simp only [ExecutionState.reindex_block_entry, Equiv.symm_symm, Equiv.symm_apply_apply]

end

end QuantumAlg.ExecutionState
