/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Instrument.Observation
import all QuantumAlg.Core.Execution.Instrument.Observation
import all QuantumAlg.Core.Base.Gate.Effect.Bounds

/-!
# Monotonicity of actual classical event observations

Pointwise event inclusion preserves the order of observation weights on the
same complete execution state, including subnormalized states of zero mass.
-/

namespace QuantumAlg.Execution

noncomputable section

/-- Pointwise inclusion of classical events increases their actual block observation weight. -/
lemma recordEvent_effectWeight_mono {Record : Type} [Fintype Record] {R : Register}
    (state : ExecutionState Record R) (event accepted : Record → Bool)
    (inclusion : ∀ record, event record = true → accepted record = true) :
    state.effectWeight (recordEventEffect R event) ≤
      state.effectWeight (recordEventEffect R accepted) := by
  unfold ExecutionState.effectWeight
  apply Finset.sum_le_sum
  intro record _
  by_cases selected : event record = true
  · exact le_of_eq (by
      rw [recordEventEffect, if_pos selected, recordEventEffect,
        if_pos (inclusion record selected)])
  · rw [recordEventEffect, if_neg selected, Effect.weight_zero]
    exact Effect.weight_nonneg _ _

end

end QuantumAlg.Execution
