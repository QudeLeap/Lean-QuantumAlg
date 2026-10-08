/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Classical state maps independent of equality decisions

Finite classical relabeling depends only on the mapped values. Different
proofs that equality is decidable do not change any quantum block or its mass.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

/-- Pointwise equal classical maps give the same state under any equality decisions. -/
public theorem executionState_mapClassical_congr_decision
    {C D : Type} [Fintype C] [Fintype D] {R : Register}
    (state : ExecutionState C R) (left right : C → D)
    (same : ∀ entry, left entry = right entry) (firstDecision secondDecision : DecidableEq D) :
    @mapClassical C D _ _ R firstDecision state left =
      @mapClassical C D _ _ R secondDecision state right := by
  have decisionEquality : firstDecision = secondDecision := Subsingleton.elim _ _
  subst secondDecision
  exact congrArg (fun update =>
    @mapClassical C D _ _ R firstDecision state update) (funext same)

end

end QuantumAlg.ExecutionState
