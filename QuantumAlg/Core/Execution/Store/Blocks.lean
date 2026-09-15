/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Interpret.Laws

/-!
# Complete actual store blocks under sequential execution

The interpreter's finite-history reassociation changes neither the actual
final store nor any entry of its quantum-reference density operator. This
permits proofs about consecutive real instructions to compose on each full
store block without imposing a history equality or forgetting correlations.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Sequential execution keeps the same complete final-store quantum-reference block. -/
theorem seq_store_marginal {kind : ProblemKind} {pre middle post : RuntimeCtx kind}
    (first : Circuit pre middle) (second : Circuit middle post)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State pre Reference History) (original : Store post) :
    (ExecutionState.filterClassical ((Circuit.seq first second).execute Reference state)
      (fun entry => entry.1 = original)).quantumMarginal =
      (ExecutionState.filterClassical
        (second.execute Reference (first.execute Reference state))
        (fun entry => entry.1 = original)).quantumMarginal := by
  let nested := second.execute Reference (first.execute Reference state)
  let update : Store post × ((History × first.Path) × second.Path) →
      Store post × (History × (first.Path × second.Path)) :=
    fun entry => (entry.1, (entry.2.1.1, (entry.2.1.2, entry.2.2)))
  have executed := congrArg
    (fun result : State post Reference (History × (Circuit.seq first second).Path) =>
      ((result.mapClassical (fun entry => entry.1)).block original).matrix)
    (execute_seq first second state)
  have composition := congrArg
    (fun result : ExecutionState (Store post) (Register.prod post.register Reference) =>
      (result.block original).matrix)
    (ExecutionState.executionState_mapClassical_comp nested update (fun entry => entry.1))
  have regrouped :
      State.mapHistory (K := History × (Circuit.seq first second).Path) nested
        (fun history => (history.1.1, (history.1.2, history.2))) =
        nested.mapClassical update :=
    congrArg (fun decision : DecidableEq (Store post × (History × (first.Path × second.Path))) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod post.register Reference)
        decision nested update) (Subsingleton.elim _ _)
  have regroupedBlock := congrArg
    (fun result : State post Reference (History × (Circuit.seq first second).Path) =>
      ((result.mapClassical (fun entry => entry.1)).block original).matrix) regrouped
  apply DensityOperator.ext
  exact (BasisSeeded.store_matrix ((Circuit.seq first second).execute Reference state)
    original).symm.trans (executed.trans (regroupedBlock.trans (composition.trans
      (BasisSeeded.store_matrix nested original))))

end

end QuantumAlg.Circuit
