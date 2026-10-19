/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Interpret.Laws
import QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Complete actual store blocks under sequential execution

The interpreter's finite-history reassociation changes neither the actual
final store nor any entry of its quantum-reference density operator. This
permits proofs about consecutive real instructions to compose on each full
store block without imposing a history equality or forgetting correlations.
-/

namespace QuantumAlg.Circuit

variable {allowAllocation : Bool}

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Sequential execution keeps the same complete final-store quantum-reference block. -/
lemma seq_store_marginal {model : ExecutionModel}
    {pre middle post : RuntimeCtx model.kind}
    (first : Circuit model pre middle allowAllocation) (second : Circuit model middle post
      allowAllocation) (environment : model.Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State pre Reference (model.HiddenState × History)) (original : Store post) :
    (ExecutionState.filterClassical ((Circuit.seq first second).execute environment Reference state)
      (fun entry => entry.1 = original)).quantumMarginal =
      (ExecutionState.filterClassical
        (second.execute environment Reference (first.execute environment Reference state))
        (fun entry => entry.1 = original)).quantumMarginal := by
  let nested := second.execute environment Reference (first.execute environment Reference state)
  let update : Store post × (model.HiddenState × ((History × first.Path) × second.Path)) →
      Store post × (model.HiddenState × (History × (first.Path × second.Path))) :=
    fun entry => (entry.1, (entry.2.1, (entry.2.2.1.1, (entry.2.2.1.2, entry.2.2.2))))
  have executed := congrArg
    (fun result : State post Reference
      (model.HiddenState × (History × (Circuit.seq first second).Path)) =>
      ((result.mapClassical (fun entry => entry.1)).block original).matrix)
    (execute_seq (environment := environment) first second state)
  have composition := congrArg
    (fun result : ExecutionState (Store post) (Register.prod post.register Reference) =>
      (result.block original).matrix)
    (ExecutionState.executionState_mapClassical_comp nested update (fun entry => entry.1))
  have regrouped :
      State.mapHistory (K := model.HiddenState × (History × (Circuit.seq first second).Path)) nested
        (fun history => (history.1, (history.2.1.1, (history.2.1.2, history.2.2)))) =
        nested.mapClassical update :=
    ExecutionState.executionState_mapClassical_congr _ rfl
  have regroupedBlock := congrArg
    (fun result : State post Reference
      (model.HiddenState × (History × (Circuit.seq first second).Path)) =>
      ((result.mapClassical (fun entry => entry.1)).block original).matrix) regrouped
  apply DensityOperator.ext
  exact (BasisSeeded.store_matrix ((Circuit.seq first second).execute environment Reference state)
    original).symm.trans (executed.trans (regroupedBlock.trans (composition.trans
      (BasisSeeded.store_matrix nested original))))

end

end QuantumAlg.Circuit
