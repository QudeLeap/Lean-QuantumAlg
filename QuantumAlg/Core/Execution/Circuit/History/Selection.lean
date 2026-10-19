/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Composition.History.Selection
import all QuantumAlg.Core.Execution.Classical.Branch.Laws
import all QuantumAlg.Core.Execution.Classical.Iteration
import all QuantumAlg.Core.Execution.Interpret.Laws

/-!
# Complete initial-history fibers of allocation-free native circuits

The equality follows the actual interpreter on arbitrary correlated inputs.
Physical Store, persistent services, external Reference and complete actual
paths remain in the state. The false allocation index excludes allocation and
workspace constructors; no locality certificate or caller assumption is used.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma branch_selectHistory {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {allowAllocation : Bool}
    {shape : CShape} (input : CInputRef pre shape)
    (body : shape.Value → Circuit model pre post allowAllocation)
    (environment : model.Environment) (Reference : Register)
    (natural : ∀ branch {H D : Type} [Fintype H] [DecidableEq D]
      (state : State pre Reference (model.HiddenState × H)) (read : H → D) (selected : D),
      ((body branch).execute environment Reference state).selectHistory
          (fun record => read record.2.1) selected =
        (body branch).execute environment Reference
          (state.selectHistory (fun record => read record.2) selected))
    {H D : Type} [Fintype H] [DecidableEq D]
    (state : State pre Reference (model.HiddenState × H)) (read : H → D) (selected : D) :
    ((Circuit.branch input body).execute environment Reference state).selectHistory
        (fun record => read record.2.1) selected =
      (Circuit.branch input body).execute environment Reference
        (state.selectHistory (fun record => read record.2) selected) := by
  let parts (branch : shape.Value) :=
    ((body branch).execute environment Reference
      (state.selectClassical (fun record => record.1.read input) branch)).mapHistory
        (fun record => (record.1, (record.2.1,
          (⟨branch, record.2.2⟩ : (Circuit.branch input body).Path))))
  have total : ∑ branch, (parts branch).mass ≤ 1 := by
    simp only [parts, State.mapHistory_mass, Circuit.execute_mass,
      ExecutionState.sum_selectClassical_mass]
    exact state.mass_le_one
  have original : (Circuit.branch input body).execute environment Reference state =
      ExecutionState.finiteSum parts total := rfl
  apply ExecutionState.ext
  intro label
  apply DensityOperator.ext
  rw [original]
  change (((ExecutionState.finiteSum parts total).selectClassical
    (fun record => read record.2.2.1) selected).block label).matrix = _
  rw [ExecutionState.selectClassical_finiteSum_block_matrix,
    Circuit.execute_branch_block_matrix]
  apply Finset.sum_congr rfl
  intro branch _
  have commutes :
      State.selectHistory (ctx := pre) (Reference := Reference)
          (state.selectClassical (fun record => record.1.read input) branch)
          (fun record => read record.2) selected =
        (state.selectHistory (fun record => read record.2) selected).selectClassical
          (fun record => record.1.read input) branch :=
    ExecutionState.selectClassical_comm state
      (fun record => record.1.read input) (fun record => read record.2.2) branch selected
  have partSelection :
      (parts branch).selectHistory (fun record => read record.2.1) selected =
        ((body branch).execute environment Reference
          ((state.selectHistory (fun record => read record.2) selected).selectClassical
            (fun record => record.1.read input) branch)).mapHistory
              (fun record => (record.1, (record.2.1,
                (⟨branch, record.2.2⟩ : (Circuit.branch input body).Path)))) := by
    dsimp only [parts]
    rw [State.selectHistory_mapHistory]
    change (((body branch).execute environment Reference
      (state.selectClassical (fun record => record.1.read input) branch)).selectHistory
        (fun record => read record.2.1) selected).mapHistory _ = _
    rw [natural, commutes]
  exact congrArg (fun result => (result.block label).matrix) partSelection

private lemma iterate_selectHistory {model : ExecutionModel}
    {ctx : RuntimeCtx model.kind} {allowAllocation : Bool}
    (body : Circuit model ctx ctx allowAllocation)
    (environment : model.Environment) (Reference : Register)
    (natural : ∀ {H D : Type} [Fintype H] [DecidableEq D]
      (state : State ctx Reference (model.HiddenState × H)) (read : H → D) (selected : D),
      (body.execute environment Reference state).selectHistory
        (fun record => read record.2.1) selected =
        body.execute environment Reference (state.selectHistory
          (fun record => read record.2) selected))
    (count : Nat) {H D : Type} [Fintype H] [DecidableEq D]
    (state : State ctx Reference (model.HiddenState × H)) (read : H → D) (selected : D) :
    ((Circuit.iterate count body).execute environment Reference state).selectHistory
        (fun record => read record.2.1) selected =
      (Circuit.iterate count body).execute environment Reference
        (state.selectHistory (fun record => read record.2) selected) := by
  induction count generalizing H with
  | zero =>
      rw [Circuit.execute_iterate_zero, State.selectHistory_mapHistory]
      rfl
  | succ count ih =>
      rw [Circuit.execute_iterate_succ, State.selectHistory_mapHistory]
      erw [ih (body.execute environment Reference state) (fun record => read record.1)]
      rw [natural, Circuit.execute_iterate_succ]

private lemma execute_selectHistory_of_fixed {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {allowAllocation : Bool}
    (code : Circuit model pre post allowAllocation)
    (environment : model.Environment) (fixed : allowAllocation = false)
    (Reference : Register)
    {H D : Type} [Fintype H] [DecidableEq D]
    (state : State pre Reference (model.HiddenState × H)) (read : H → D) (selected : D) :
    (code.execute environment Reference state).selectHistory
      (fun record => read record.2.1) selected =
      code.execute environment Reference (state.selectHistory
        (fun record => read record.2) selected) := by
  induction code generalizing Reference H D with
  | id =>
      dsimp only [execute, interpret, preserveService]
      rw [State.selectHistory_mapHistory]
      change (state.skip.selectHistory (fun record => read record.1.2) selected).mapHistory _ = _
      rw [State.selectHistory_skip state (fun record => read record.2) selected]
  | classical application =>
      dsimp only [execute, interpret, preserveService]
      rw [State.selectHistory_mapHistory]
      change ((nativeStep application state).selectHistory
        (fun record => read record.1.2) selected).mapHistory _ = _
      rw [State.selectHistory_nativeStep application state (fun record => read record.2) selected]
  | classicalQuery application =>
      exact State.selectHistory_queryStep environment.classical application state read selected
  | unitary program =>
      dsimp only [execute, interpret, preserveService]
      rw [State.selectHistory_mapHistory]
      change ((state.unitary (program.matrix environment.quantum)).selectHistory
        (fun record => read record.1.2) selected).mapHistory _ = _
      rw [State.selectHistory_unitary state (program.matrix environment.quantum)
        (fun record => read record.2) selected]
  | measureZ wire output =>
      dsimp only [execute, interpret, preserveService]
      rw [State.selectHistory_mapHistory]
      change ((state.measureZ wire output).selectHistory
        (fun record => read record.1.2) selected).mapHistory _ = _
      rw [State.selectHistory_measureZ state wire output (fun record => read record.2) selected]
  | retain | prepareZero | workspace => cases fixed
  | seq first second firstIH secondIH =>
      rw [execute_seq, State.selectHistory_mapHistory]
      erw [secondIH environment fixed Reference (first.execute environment Reference state)
        (fun record => read record.1) selected]
      rw [firstIH environment fixed Reference state read selected, execute_seq]
  | branch input body bodyIH =>
      exact branch_selectHistory input body environment Reference
        (fun branch {_ _} _ _ original read selected =>
          bodyIH branch environment fixed Reference original read selected) state read selected
  | iterate count body bodyIH =>
      exact iterate_selectHistory body environment Reference
        (fun {_ _} _ _ original read selected =>
          bodyIH environment fixed Reference original read selected) count state read selected
  | embed placement body bodyIH =>
      exact embedPreserving_selectHistory placement Reference
        (fun original => interpret body environment _ original)
        (fun {_ _} _ _ original read selected =>
          bodyIH environment rfl _ original read selected) state read selected
  | parallelClassical join separate first second firstIH secondIH =>
      exact parallelPreserving_selectHistory join separate
        (fun original => interpret first
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _ original)
        (fun original => interpret second
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _ original)
        (fun {_ _} _ _ original read selected =>
          firstIH
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩
          rfl _ original read selected)
        (fun {_ _} _ _ original read selected =>
          secondIH
          ⟨environment.quantum, join.interpretationRight environment.classical⟩
          rfl _ original read selected) state read selected
  | parallelQuantum join separate first second firstIH secondIH =>
      exact parallelPreserving_selectHistory join separate
        (fun original => interpret first
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ _ original)
        (fun original => interpret second
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ _ original)
        (fun {_ _} _ _ original read selected =>
          firstIH
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩
          rfl _ original read selected)
        (fun {_ _} _ _ original read selected =>
          secondIH
          ⟨environment.quantum, join.interpretationRight environment.classical⟩
          rfl _ original read selected) state read selected

/-- Every earlier-history fiber follows the same complete allocation-free execution. -/
lemma execute_selectHistory {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post false)
    (environment : model.Environment) (Reference : Register)
    {H D : Type} [Fintype H] [DecidableEq D]
    (state : State pre Reference (model.HiddenState × H)) (read : H → D) (selected : D) :
    (code.execute environment Reference state).selectHistory
      (fun record => read record.2.1) selected =
      code.execute environment Reference (state.selectHistory
        (fun record => read record.2) selected) :=
  execute_selectHistory_of_fixed code environment rfl Reference state read selected

end

end QuantumAlg.Circuit
