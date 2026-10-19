/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.Store.Blocks
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.State.History

/-!
# Full stored quantum blocks under mathematical history changes

Only mathematical history labels are summed. Actual storage, hidden service
state and the complete quantum register and external reference are retained.
Sequence association changes its recorded path, rather than the real program.
-/

namespace QuantumAlg.Execution.State

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma mapHistory_store_decision {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {H K : Type} [Fintype H] [Fintype K]
    (decision : DecidableEq (Store ctx × K)) (state : State ctx Reference H) (update : H → K) :
    @ExecutionState.mapClassical (Store ctx × H) (Store ctx × K) _ _
        (Register.prod ctx.register Reference) decision state
        (fun record => (record.1, update record.2)) = state.mapHistory update := by
  unfold mapHistory
  exact congrArg
    (fun selected : DecidableEq (Store ctx × K) =>
      @ExecutionState.mapClassical (Store ctx × H) (Store ctx × K) _ _
        (Register.prod ctx.register Reference) selected state
        (fun record => (record.1, update record.2)))
    (Subsingleton.elim _ _)


/-- Arbitrary finite history remapping preserves every complete actual store block. -/
lemma mapHistory_store_marginal {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {H K : Type} [Fintype H] [Fintype K]
    (state : State ctx Reference H) (update : H → K) (stored : Store ctx) :
    (ExecutionState.filterClassical (state.mapHistory update)
      (fun entry => entry.1 = stored)).quantumMarginal =
      (ExecutionState.filterClassical state
        (fun entry => entry.1 = stored)).quantumMarginal := by
  apply DensityOperator.ext
  refine (BasisSeeded.store_matrix (state.mapHistory update) stored).symm.trans ?_
  have composed := congrArg
    (fun result : ExecutionState (Store ctx) (ctx.register.prod Reference) =>
      (result.block stored).matrix)
    (ExecutionState.executionState_mapClassical_comp state
      (fun entry => (entry.1, update entry.2)) (fun entry => entry.1))
  exact composed.trans (BasisSeeded.store_matrix state stored)

end

end QuantumAlg.Execution.State

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Existing history naturality retains the complete actual final-store density. -/
lemma execute_mapHistory_store_marginal {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {allowAllocation : Bool}
    (program : Circuit model pre post allowAllocation) (environment : model.Environment)
    {Reference : Register}
    {H K : Type} [Fintype H] [Fintype K]
    (state : State pre Reference (model.HiddenState × H)) (update : H → K)
    (stored : Store post) :
    (ExecutionState.filterClassical
      (program.execute environment Reference
        (state.mapHistory (fun record => (record.1, update record.2))))
      (fun entry => entry.1 = stored)).quantumMarginal =
      (ExecutionState.filterClassical (program.execute environment Reference state)
        (fun entry => entry.1 = stored)).quantumMarginal := by
  rw [execute_mapHistory, State.mapHistory_store_marginal]

/-- Actual continuations depend on complete input store/service blocks, not mathematical history. -/
lemma execute_equal_store_hidden_blocks {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {allowAllocation : Bool}
    (program : Circuit model pre post allowAllocation) (environment : model.Environment)
    {Reference : Register}
    {H K : Type} [Fintype H] [Fintype K]
    (left : State pre Reference (model.HiddenState × H))
    (right : State pre Reference (model.HiddenState × K))
    (agreement : left.mapClassical (fun entry => (entry.1, entry.2.1)) =
      right.mapClassical (fun entry => (entry.1, entry.2.1))) (stored : Store post) :
    (ExecutionState.filterClassical (program.execute environment Reference left)
      (fun entry => entry.1 = stored)).quantumMarginal =
      (ExecutionState.filterClassical (program.execute environment Reference right)
        (fun entry => entry.1 = stored)).quantumMarginal := by
  have compressed := congrArg
    (fun state : ExecutionState (Store pre × model.HiddenState) (pre.register.prod Reference) =>
      state.mapClassical (fun entry => (entry.1, (entry.2, ())))) agreement
  rw [ExecutionState.executionState_mapClassical_comp,
    ExecutionState.executionState_mapClassical_comp] at compressed
  have compressedHistory : left.mapHistory (fun record => (record.1, ())) =
      right.mapHistory (fun record => (record.1, ())) := by
    calc
      _ = left.mapClassical (fun entry => (entry.1, (entry.2.1, ()))) := by
        exact (State.mapHistory_store_decision (ctx := pre) (Reference := Reference)
          (H := model.HiddenState × H) (K := model.HiddenState × Unit)
          _ left (fun record => (record.1, ()))).symm
      _ = right.mapClassical (fun entry => (entry.1, (entry.2.1, ()))) := by
        simpa only [Function.comp_def] using compressed
      _ = _ := by
        exact State.mapHistory_store_decision (ctx := pre) (Reference := Reference)
          (H := model.HiddenState × K) (K := model.HiddenState × Unit)
          _ right (fun record => (record.1, ()))
  calc
    _ = (ExecutionState.filterClassical
        (program.execute environment Reference (left.mapHistory (fun record => (record.1, ()))))
        (fun entry => entry.1 = stored)).quantumMarginal :=
      (execute_mapHistory_store_marginal program environment left (fun _ => ()) stored).symm
    _ = (ExecutionState.filterClassical
        (program.execute environment Reference (right.mapHistory (fun record => (record.1, ()))))
        (fun entry => entry.1 = stored)).quantumMarginal := by rw [compressedHistory]
    _ = _ := execute_mapHistory_store_marginal program environment right (fun _ => ()) stored

/-- Three literal instructions have the same complete stored density under reassociation. -/
lemma seq_assoc_store_marginal {model : ExecutionModel}
    {origin first second final : RuntimeCtx model.kind} {allowAllocation : Bool}
    (priorCode : Circuit model origin first allowAllocation)
    (middle : Circuit model first second allowAllocation)
    (tail : Circuit model second final allowAllocation) (environment : model.Environment)
    {Reference : Register}
    {H : Type} [Fintype H]
    (state : State origin Reference (model.HiddenState × H)) (stored : Store final) :
    (ExecutionState.filterClassical
      ((priorCode.seq (middle.seq tail)).execute environment Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal =
      (ExecutionState.filterClassical
        (((priorCode.seq middle).seq tail).execute environment Reference state)
        (fun entry => entry.1 = stored)).quantumMarginal := by
  simp only [execute_seq]
  erw [State.mapHistory_store_marginal, State.mapHistory_store_marginal,
    State.mapHistory_store_marginal]
  exact (execute_mapHistory_store_marginal tail environment
    (middle.execute environment Reference (priorCode.execute environment Reference state))
    (fun history => (history.1.1, (history.1.2, history.2))) stored).symm

end

end QuantumAlg.Circuit
