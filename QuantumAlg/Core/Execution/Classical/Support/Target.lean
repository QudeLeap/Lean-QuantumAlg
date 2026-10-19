/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Support

namespace QuantumAlg.ExecutionState

noncomputable section

/-- A target depending only on the observed result survives summing every unobserved store. -/
lemma mapClassical_mixed_target {C D : Type} [Fintype C] [Fintype D] [DecidableEq D]
    {R : Register} (state : ExecutionState C R) (read : C → D)
    (target : D → DensityOperator R) (normalized : ∀ value, (target value).IsNormalized)
    (holds : ∀ entry, (StatePromise.mixed (target (read entry))
      (normalized (read entry))).Holds (state.block entry)) (result : D) :
    (StatePromise.mixed (target result) (normalized result)).Holds
      ((state.mapClassical read).block result) := by
  change ((state.mapClassical read).block result).matrix =
    ((state.mapClassical read).block result).mass • (target result).matrix
  rw [ExecutionState.mapClassical_block_matrix, ExecutionState.mapClassical_block_mass,
    Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro entry _
  by_cases selected : read entry = result
  · simp only [selected, if_true]
    have actual := holds entry
    change (state.block entry).matrix =
      (state.block entry).mass • (target (read entry)).matrix at actual
    simpa only [selected] using actual
  · simp only [selected, if_false, zero_smul]

end

end QuantumAlg.ExecutionState
