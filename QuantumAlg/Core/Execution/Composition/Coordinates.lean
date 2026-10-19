/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.State.Coordinates
import all QuantumAlg.Core.Execution.State

/-!
# Exact coordinate transport independent of equality decisions

The classical pushforward is the same finite sum under every equality
decision. This form lets composition proofs use the actual sealed map and
history interfaces without imposing a particular decision implementation.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

/-- Reference-coordinate transport commutes with the same actual classical pushforward. -/
lemma composition_reindex_mapClassical {C D : Type} [Fintype C] [Fintype D]
    {R S : Register} (state : ExecutionState C R) (basis : R.Index ≃ S.Index)
    (labels : C → D) (firstDecision secondDecision : DecidableEq D) :
    @mapClassical C D _ _ S firstDecision (state.reindex basis) labels =
      (@mapClassical C D _ _ R secondDecision state labels).reindex basis := by
  cases Subsingleton.elim firstDecision secondDecision
  exact @coordinate_reindex_mapClassical C D _ _ firstDecision R S state basis labels

end

end QuantumAlg.ExecutionState

namespace QuantumAlg.Execution.State

noncomputable section

/-- The unchanged history operation uses the same full reference coordinates on both sides. -/
lemma composition_reindex_mapHistory {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference Other : Register} {H K : Type} [Fintype H] [Fintype K]
    (state : State ctx Reference H)
    (basis : (Register.prod ctx.register Reference).Index ≃
      (Register.prod ctx.register Other).Index) (update : H → K) :
    State.mapHistory (ctx := ctx) (Reference := Other) (state.reindex basis) update =
      (state.mapHistory update).reindex basis := by
  unfold mapHistory
  exact ExecutionState.composition_reindex_mapClassical state basis _ _ _

end

end QuantumAlg.Execution.State
