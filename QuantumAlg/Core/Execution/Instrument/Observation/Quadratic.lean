/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Observation

/-!
# The original classical event on a complete raw quantum vector

The event selects the certain or impossible effect. Its quadratic weight
retains the norm of the entire vector, including arbitrary coherent
collisions and external references, without a normalization premise.
-/

namespace QuantumAlg.Execution

noncomputable section

/-- A classical event observes all raw-vector mass exactly when that event holds. -/
lemma recordEventEffect_quadratic {Record : Type} {R : Register}
    (event : Record → Bool) (record : Record) (vector : HilbertVector R) :
    HilbertOperator.quadraticWeight (recordEventEffect R event record).matrix vector =
      if event record = true then ‖vector‖ ^ 2 else 0 := by
  by_cases accepted : event record = true
  · simp only [recordEventEffect, if_pos accepted]
    change (inner ℂ vector ((1 : HilbertOperator R).applyVec vector)).re = ‖vector‖ ^ 2
    rw [HilbertOperator.one_applyVec]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) vector
  · simp only [recordEventEffect, if_neg accepted]
    change (inner ℂ vector ((0 : HilbertOperator R).applyVec vector)).re = 0
    have zeroAction : (0 : HilbertOperator R).applyVec vector = 0 := by
      ext index
      simp [HilbertOperator.applyVec_apply]
    rw [zeroAction, inner_zero_right]
    rfl

end

end QuantumAlg.Execution
