/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.State.History
import all QuantumAlg.Core.Execution.Classical.Iteration
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Composition.History
import all QuantumAlg.Core.Execution.Composition.Parallel
import all QuantumAlg.Core.Execution.Composition.Embedding
import all QuantumAlg.Core.Execution.Interpret.Preserving

/-!
# History naturality of the single circuit interpreter

Every existing circuit commutes with an arbitrary function on its finite
input history while retaining the oracle state independently. The final store,
quantum/reference matrix, current oracle state and newly recorded
execution path are unchanged. Noninjective history functions retain the
actual sum of the identified density blocks. The proof follows the original
interpreter, including real allocation, branch selection and workspace exit.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma branch_history {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {allowAllocation : Bool}
    {shape : CShape} (input : CInputRef pre shape)
    (body : shape.Value → Circuit model pre post allowAllocation)
    (environment : model.Environment) (Reference : Register)
    (natural : ∀ value {H K : Type} [Fintype H] [Fintype K]
      (state : State pre Reference (model.HiddenState × H)) (update : H → K),
      (body value).execute environment Reference
        (state.mapHistory (fun record => (record.1, update record.2))) =
        ((body value).execute environment Reference state).mapHistory
          (fun record => (record.1, (update record.2.1, record.2.2))))
    {H K : Type} [Fintype H] [Fintype K]
    (state : State pre Reference (model.HiddenState × H)) (update : H → K) :
    (Circuit.branch input body).execute environment Reference
      (state.mapHistory (fun record => (record.1, update record.2))) =
      ((Circuit.branch input body).execute environment Reference state).mapHistory
        (fun record => (record.1, (update record.2.1, record.2.2))) := by
  let parts (value : shape.Value) :
      State post Reference (model.HiddenState × (H × (Circuit.branch input body).Path)) :=
    ((body value).execute environment Reference
      (state.selectClassical (fun record => record.1.read input) value)).mapHistory
        (fun record => (record.1, (record.2.1, ⟨value, record.2.2⟩)))
  let resultMap : model.HiddenState × (H × (Circuit.branch input body).Path) →
      model.HiddenState × (K × (Circuit.branch input body).Path) :=
    fun record => (record.1, (update record.2.1, record.2.2))
  have total : ∑ value, (parts value).mass ≤ 1 := by
    simp only [parts, State.mapHistory_mass, execute_mass, ExecutionState.sum_selectClassical_mass]
    exact state.mass_le_one
  have original : (Circuit.branch input body).execute environment Reference state =
      ExecutionState.finiteSum parts total := by
    rfl
  have mappedTotal : ∑ value, ((parts value).mapHistory resultMap).mass ≤ 1 := by
    simpa only [State.mapHistory_mass] using total
  have mapped : (Circuit.branch input body).execute environment Reference
        (state.mapHistory (fun record => (record.1, update record.2))) =
      ExecutionState.finiteSum (fun value => (parts value).mapHistory resultMap) mappedTotal := by
    apply ExecutionState.ext
    intro result
    apply DensityOperator.ext
    rw [execute_branch_block_matrix, ExecutionState.finiteSum_block_matrix]
    apply Finset.sum_congr rfl
    intro value _
    have actual :=
      (congrArg (fun selected : State pre Reference (model.HiddenState × K) =>
        (body value).execute environment Reference selected)
        (State.mapHistory_selectClassical state
          (fun record => (record.1, update record.2)) input value)).trans
          (natural value
            (state.selectClassical (fun record => record.1.read input) value) update)
    have contribution := congrArg
      (fun output : State post Reference (model.HiddenState × (K × (body value).Path)) =>
        ((output.mapHistory (fun record =>
          (record.1, (record.2.1,
            (⟨value, record.2.2⟩ : (Circuit.branch input body).Path))))).block result).matrix)
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

private lemma iterate_history {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    {allowAllocation : Bool}
    (body : Circuit model ctx ctx allowAllocation)
    (environment : model.Environment) (Reference : Register)
    (natural : ∀ {H K : Type} [Fintype H] [Fintype K]
      (state : State ctx Reference (model.HiddenState × H)) (update : H → K),
      body.execute environment Reference
        (state.mapHistory (fun record => (record.1, update record.2))) =
        (body.execute environment Reference state).mapHistory
          (fun record => (record.1, (update record.2.1, record.2.2))))
    (count : Nat) {H K : Type} [Fintype H] [Fintype K]
    (state : State ctx Reference (model.HiddenState × H)) (update : H → K) :
    (Circuit.iterate count body).execute environment Reference
      (state.mapHistory (fun record => (record.1, update record.2))) =
      ((Circuit.iterate count body).execute environment Reference state).mapHistory
        (fun record => (record.1, (update record.2.1, record.2.2))) := by
  induction count generalizing H K with
  | zero =>
      rw [execute_iterate_zero, execute_iterate_zero]
      simp only [State.mapHistory_comp, Function.comp_def]
  | succ count ih =>
      rw [execute_iterate_succ, natural,
        ih (body.execute environment Reference state) (fun record => (update record.1, record.2)),
        execute_iterate_succ]
      simp only [State.mapHistory_comp, Function.comp_def]

/-- Existing execution commutes with any finite history map, preserving its full actual path. -/
lemma execute_mapHistory {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {allowAllocation : Bool}
    (code : Circuit model pre post allowAllocation)
    (environment : model.Environment) (Reference : Register)
    {H K : Type} [Fintype H] [Fintype K]
    (state : State pre Reference (model.HiddenState × H)) (update : H → K) :
    code.execute environment Reference
      (state.mapHistory (fun record => (record.1, update record.2))) =
      (code.execute environment Reference state).mapHistory
        (fun record => (record.1, (update record.2.1, record.2.2))) := by
  induction code generalizing Reference H K with
  | id =>
      dsimp only [execute, interpret, preserveService]
      rw [State.mapHistory_skip]
      simp only [State.mapHistory_comp, Function.comp_def]
      exact ExecutionState.executionState_mapClassical_congr _ rfl
  | classical application =>
      dsimp only [execute, interpret, preserveService]
      rw [State.mapHistory_nativeStep]
      simp only [State.mapHistory_comp, Function.comp_def]
      exact ExecutionState.executionState_mapClassical_congr _ rfl
  | classicalQuery application =>
      exact State.mapHistory_queryStep environment.classical application state update
  | unitary program =>
      dsimp only [execute, interpret, preserveService]
      rw [State.mapHistory_unitary]
      simp only [State.mapHistory_comp, Function.comp_def]
      exact ExecutionState.executionState_mapClassical_congr _ rfl
  | measureZ wire output =>
      dsimp only [execute, interpret, preserveService]
      rw [State.mapHistory_measureZ]
      simp only [State.mapHistory_comp, Function.comp_def]
      exact ExecutionState.executionState_mapClassical_congr _ rfl
  | retain _ key shape fresh =>
      dsimp only [execute, interpret, preserveService]
      rw [State.mapHistory_retain]
      simp only [State.mapHistory_comp, Function.comp_def]
      exact ExecutionState.executionState_mapClassical_congr _ rfl
  | prepareZero _ key layout fresh disjoint =>
      dsimp only [execute, interpret, preserveService]
      rw [State.mapHistory_prepare]
      simp only [State.mapHistory_comp, Function.comp_def]
      exact ExecutionState.executionState_mapClassical_congr _ rfl
  | seq first second firstIH secondIH =>
      rw [execute_seq, firstIH,
        secondIH environment Reference (first.execute environment Reference state)
          (fun record => (update record.1, record.2)),
        execute_seq]
      simp only [State.mapHistory_comp, Function.comp_def]
  | branch input body bodyIH =>
      exact branch_history input body environment Reference
        (fun value {_ _} _ _ original update =>
          bodyIH value environment Reference original update) state update
  | iterate count body bodyIH =>
      exact iterate_history body environment Reference
        (fun {_ _} _ _ original update => bodyIH environment Reference original update)
        count state update
  | workspace _ key shape fresh body bodyIH =>
      change State.popWorkspace key shape fresh
          (body.execute environment Reference
            ((state.mapHistory (fun record => (record.1, update record.2))).pushWorkspace
              key shape fresh)) =
        (State.popWorkspace key shape fresh
          (body.execute environment Reference (state.pushWorkspace key shape fresh))).mapHistory
            (fun record => (record.1, (update record.2.1, record.2.2)))
      rw [State.mapHistory_pushWorkspace, bodyIH,
        State.mapHistory_popWorkspace]
  | embed placement body bodyIH =>
      exact embedPreserving_history placement Reference
        (fun original => interpret body environment _ original)
        (fun {_ _} _ _ original update => bodyIH environment _ original update) state update
  | parallelClassical join separate first second firstIH secondIH =>
      exact parallelPreserving_history join separate
        (fun original => interpret first
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _ original)
        (fun original => interpret second
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _ original)
        (fun {_ _} _ _ original update => firstIH
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _ original update)
        (fun {_ _} _ _ original update => secondIH
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _ original update)
        state update
  | parallelQuantum join separate first second firstIH secondIH =>
      exact parallelPreserving_history join separate
        (fun original => interpret first
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _ original)
        (fun original => interpret second
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _ original)
        (fun {_ _} _ _ original update => firstIH
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _ original update)
        (fun {_ _} _ _ original update => secondIH
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _ original update)
        state update

end

end QuantumAlg.Circuit
