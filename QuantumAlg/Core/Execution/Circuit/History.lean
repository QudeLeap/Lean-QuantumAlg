/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.State.History
import all QuantumAlg.Core.Execution.Classical.Iteration
import all QuantumAlg.Core.Execution.Interpret.Laws

/-!
# History naturality of the single circuit interpreter

Every existing circuit commutes with an arbitrary function on its finite
input history. The final store, quantum/reference matrix and newly recorded
execution path are unchanged. Noninjective history functions retain the
actual sum of the identified density blocks. The proof follows the original
interpreter, including real allocation, branch selection and workspace exit.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem branch_history {kind : ProblemKind} {pre post : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef pre shape) (body : shape.Value → Circuit pre post)
    (Reference : Register)
    (natural : ∀ value {H K : Type} [Fintype H] [Fintype K]
      (state : State pre Reference H) (update : H → K),
      (body value).execute Reference (state.mapHistory update) =
        ((body value).execute Reference state).mapHistory
          (fun record => (update record.1, record.2)))
    {H K : Type} [Fintype H] [Fintype K]
    (state : State pre Reference H) (update : H → K) :
    (Circuit.branch input body).execute Reference (state.mapHistory update) =
      ((Circuit.branch input body).execute Reference state).mapHistory
        (fun record => (update record.1, record.2)) := by
  let parts (value : shape.Value) : State post Reference (H × (Circuit.branch input body).Path) :=
    ((body value).execute Reference
      (state.selectClassical (fun record => record.1.read input) value)).mapHistory
        (fun record => (record.1, ⟨value, record.2⟩))
  let resultMap : H × (Circuit.branch input body).Path →
      K × (Circuit.branch input body).Path := fun record => (update record.1, record.2)
  have total : ∑ value, (parts value).mass ≤ 1 := by
    simp only [parts, State.mapHistory_mass, execute_mass, ExecutionState.sum_selectClassical_mass]
    exact state.mass_le_one
  have original : (Circuit.branch input body).execute Reference state =
      ExecutionState.finiteSum parts total := by
    rfl
  have mappedTotal : ∑ value, ((parts value).mapHistory resultMap).mass ≤ 1 := by
    simpa only [State.mapHistory_mass] using total
  have mapped : (Circuit.branch input body).execute Reference (state.mapHistory update) =
      ExecutionState.finiteSum (fun value => (parts value).mapHistory resultMap) mappedTotal := by
    apply ExecutionState.ext
    intro result
    apply DensityOperator.ext
    rw [execute_branch_block_matrix, ExecutionState.finiteSum_block_matrix]
    apply Finset.sum_congr rfl
    intro value _
    have actual :=
      (congrArg (fun selected : State pre Reference K => (body value).execute Reference selected)
        (State.mapHistory_selectClassical state update input value)).trans
          (natural value
            (state.selectClassical (fun record => record.1.read input) value) update)
    have contribution := congrArg
      (fun output : State post Reference (K × (body value).Path) =>
        ((output.mapHistory (fun record =>
          (record.1, (⟨value, record.2⟩ : (Circuit.branch input body).Path)))).block result).matrix)
      actual
    simpa only [parts, resultMap, State.mapHistory_comp, Function.comp_def] using contribution
  calc
    _ = ExecutionState.finiteSum (fun value => (parts value).mapHistory resultMap) mappedTotal :=
      mapped
    _ = State.mapHistory (ExecutionState.finiteSum parts total) resultMap := by
      convert (ExecutionState.mapClassical_finiteSum parts total
        (fun record => (record.1, resultMap record.2))).symm using 1 <;>
        dsimp only [State.mapHistory] <;>
        congr! 2
      apply ExecutionState.ext
      intro label
      apply DensityOperator.ext
      simp only [ExecutionState.finiteSum, ExecutionState.mapClassical_block_matrix]
      apply Finset.sum_congr rfl
      intro index _
      apply Finset.sum_congr rfl
      intro entry _
      split_ifs <;> rfl
    _ = _ := congrArg (fun output => output.mapHistory resultMap) original.symm

private theorem iterate_history {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (body : Circuit ctx ctx) (Reference : Register)
    (natural : ∀ {H K : Type} [Fintype H] [Fintype K]
      (state : State ctx Reference H) (update : H → K),
      body.execute Reference (state.mapHistory update) =
        (body.execute Reference state).mapHistory (fun record => (update record.1, record.2)))
    (count : Nat) {H K : Type} [Fintype H] [Fintype K]
    (state : State ctx Reference H) (update : H → K) :
    (Circuit.iterate count body).execute Reference (state.mapHistory update) =
      ((Circuit.iterate count body).execute Reference state).mapHistory
        (fun record => (update record.1, record.2)) := by
  induction count generalizing H K with
  | zero =>
      rw [execute_iterate_zero, execute_iterate_zero]
      simp only [State.mapHistory_comp, Function.comp_def]
  | succ count ih =>
      rw [execute_iterate_succ, natural, ih, execute_iterate_succ]
      simp only [State.mapHistory_comp, Function.comp_def]

/-- Existing execution commutes with any finite history map, preserving its full actual path. -/
theorem execute_mapHistory {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (Reference : Register) {H K : Type} [Fintype H] [Fintype K]
    (state : State pre Reference H) (update : H → K) :
    code.execute Reference (state.mapHistory update) =
      (code.execute Reference state).mapHistory (fun record => (update record.1, record.2)) := by
  induction code generalizing H K with
  | id => exact State.mapHistory_skip state update
  | classical operation => exact State.mapHistory_classicalStep state update operation
  | declaredCall call => exact State.mapHistory_declaredStep state update call
  | unitary program _ => exact State.mapHistory_unitary state update program
  | measureZ wire output => exact State.mapHistory_measureZ state update wire output
  | randomBits width output => exact State.mapHistory_randomBits state update width output
  | retain _ key shape fresh => exact State.mapHistory_retain state update key shape fresh
  | prepare _ key layout fresh disjoint preparation =>
      exact State.mapHistory_prepare state update key layout fresh disjoint preparation
  | seq first second firstIH secondIH =>
      rw [execute_seq, firstIH, secondIH, execute_seq]
      simp only [State.mapHistory_comp, Function.comp_def]
  | branch input body bodyIH =>
      exact branch_history input body Reference
        (fun value {_ _} _ _ original update => bodyIH value original update) state update
  | iterate count body bodyIH =>
      exact iterate_history body Reference
        (fun {_ _} _ _ original update => bodyIH original update)
        count state update
  | workspace _ key shape fresh body bodyIH =>
      change State.popWorkspace key shape fresh
          (body.execute Reference ((state.mapHistory update).pushWorkspace key shape fresh)) =
        (State.popWorkspace key shape fresh
          (body.execute Reference (state.pushWorkspace key shape fresh))).mapHistory
            (fun record => (update record.1, record.2))
      rw [State.mapHistory_pushWorkspace, bodyIH,
        State.mapHistory_popWorkspace]

end

end QuantumAlg.Circuit
