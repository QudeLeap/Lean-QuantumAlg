/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Random
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Summing an independent finite classical choice

Discarding a mathematical sample index sums its uniformly weighted blocks
back to the original execution state. This operation changes no runtime
context or live storage. It also preserves any classical observation that
ignores the sample, together with its complete quantum-reference blocks.
-/

namespace QuantumAlg.Execution

noncomputable section

/-- Summing the independent finite choice restores exactly the original execution state. -/
theorem uniformChoice_map_fst {C : Type} [Fintype C] [DecidableEq C] {R : Register}
    (state : ExecutionState C R) (count : ℕ+) :
    (uniformChoice state count).mapClassical Prod.fst = state := by
  have coefficient : (∑ _outcome : Fin count, (count : ℝ)⁻¹) = (1 : ℝ) := by
    have positive : (0 : ℝ) < count := by exact_mod_cast count.pos
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ (ne_of_gt positive)
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  rw [ExecutionState.mapClassical_block_matrix, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single result]
  · simp only [uniformChoice_block_matrix, if_true]
    rw [← Finset.sum_smul, coefficient, one_smul]
  · intro other _ different
    simp only [if_neg different, Finset.sum_const_zero]
  · intro absent
    exact False.elim (absent (Finset.mem_univ result))

/-- Any observation that ignores the independent sample retains its exact prior state. -/
theorem uniformChoice_map_ignore {C D : Type} [Fintype C] [Fintype D]
    [DecidableEq D] {R : Register}
    (state : ExecutionState C R) (count : ℕ+) (update : C → D) :
    (uniformChoice state count).mapClassical (fun entry => update entry.1) =
      state.mapClassical update := by
  classical
  exact (ExecutionState.executionState_mapClassical_comp
    (uniformChoice state count) Prod.fst update).symm.trans
      (congrArg (fun prior => prior.mapClassical update) (uniformChoice_map_fst state count))

end
end QuantumAlg.Execution
