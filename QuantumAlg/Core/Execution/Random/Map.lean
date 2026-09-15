/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Random
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Independent finite sampling and deterministic classical maps

A deterministic map may precede or follow an independent finite uniform
choice. The equality preserves every complete quantum block, with the same
uniform scalar and the same sum over the deterministic map's input fiber.
It is a law of the existing state operations and adds no execution syntax.
-/

namespace QuantumAlg.Execution

noncomputable section

/-- Independent finite sampling commutes with a deterministic map of the prior classical index. -/
theorem uniformChoice_mapClassical {C D : Type} [Fintype C] [Fintype D]
    [DecidableEq D] {R : Register} (state : ExecutionState C R) (count : ℕ+)
    [DecidableEq (D × Fin count)] (update : C → D) :
    uniformChoice (state.mapClassical update) count =
      (uniformChoice state count).mapClassical (fun entry => (update entry.1, entry.2)) := by
  classical
  apply ExecutionState.ext
  intro result
  obtain ⟨result, outcome⟩ := result
  apply DensityOperator.ext
  rw [uniformChoice_block_matrix, ExecutionState.mapClassical_block_matrix,
    ExecutionState.mapClassical_block_matrix, Fintype.sum_prod_type, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro entry _
  by_cases selected : update entry = result
  · simp [selected, uniformChoice_block_matrix]
  · simp [selected]

end

end QuantumAlg.Execution
