/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.State.Coordinates
import all QuantumAlg.Core.Execution.Reference.Unitary
import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Execution.Classical.Iteration
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Reference basis naturality of actual circuit execution

Changing only the external reference coordinates commutes with every existing
instruction. Complete classical blocks, actual storage updates and the original
finite execution paths are retained. The proof follows the same interpreter;
no product-state, nonempty-reference or support assumption is imposed
[dW19, qcnotes.tex:5381,5405,5409,8071].
-/

namespace QuantumAlg

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace ExecutionState

private theorem reference_map {A B : Type} [Fintype A] [Fintype B] {R S : Register}
    (leftDecision rightDecision : DecidableEq B) (state : ExecutionState A R)
    (basis : R.Index ≃ S.Index) (update : A → B) :
    @ExecutionState.mapClassical A B _ _ S leftDecision (state.reindex (S := S) basis) update =
      (@ExecutionState.mapClassical A B _ _ R rightDecision state update).reindex
        (S := S) basis := by
  cases Subsingleton.elim leftDecision rightDecision
  exact @ExecutionState.coordinate_reindex_mapClassical A B _ _ leftDecision R S state basis update

private theorem reference_select {C D : Type} [Fintype C] [DecidableEq D]
    {R S : Register} (state : ExecutionState C R) (basis : R.Index ≃ S.Index)
    (read : C → D) (selected : D) :
    (state.reindex (S := S) basis).selectClassical read selected =
      (state.selectClassical read selected).reindex (S := S) basis := by
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  simp only [selectClassical_block, reindex_block_entry,
    apply_ite DensityOperator.matrix]
  split <;> rfl

private theorem reference_kernel {C Outcome : Type} [Fintype C] [Fintype Outcome]
    {R S : Register} (state : ExecutionState C R) (basis : R.Index ≃ S.Index)
    (transition : C → PMF Outcome) :
    kernelChoice (state.reindex (S := S) basis) transition =
      (kernelChoice state transition).reindex (S := S) basis := by
  apply ExecutionState.ext
  rintro ⟨value, outcome⟩
  apply DensityOperator.ext
  ext row column
  simp only [kernelChoice_block_matrix, reindex_block_entry, Matrix.smul_apply]

private theorem reference_unitary {C : Type} [Fintype C] {R Reference Other : Register}
    (state : ExecutionState C (R.prod Reference))
    (basis : Reference.Index ≃ Other.Index) (program : C → UnitaryOperator R) :
    (state.reindex (S := R.prod Other) ((Equiv.refl R.Index).prodCongr basis)).applyUnitary
        (fun value => UnitaryOperator.prodTensor (program value) (1 : UnitaryOperator Other)) =
      (state.applyUnitary (fun value =>
        UnitaryOperator.prodTensor (program value) (1 : UnitaryOperator Reference))).reindex
          (S := R.prod Other)
          ((Equiv.refl R.Index).prodCongr basis) := by
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  change (DensityOperator.applyUnitary
    (UnitaryOperator.prodTensor (program value) (1 : UnitaryOperator Other))
      ((state.reindex (S := R.prod Other)
        ((Equiv.refl R.Index).prodCongr basis)).block value)).matrix
        (row.1, row.2) (column.1, column.2) =
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (program value) (1 : UnitaryOperator Reference))
        (state.block value)).matrix (row.1, basis.symm row.2) (column.1, basis.symm column.2)
  rw [DensityOperator.localUnitary_block, DensityOperator.localUnitary_block]
  rfl

private theorem reference_measure {C O : Type} [Fintype C] [Fintype O] [DecidableEq O]
    {R S : Register} (state : ExecutionState C R) (basis : R.Index ≃ S.Index)
    (original : R.Index → O) (transported : S.Index → O)
    (reads : ∀ value, original (basis.symm value) = transported value) :
    (state.reindex (S := S) basis).measureZ transported =
      (state.measureZ original).reindex (S := S) basis := by
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  change (ZMeasurement.branch transported value.2
      ((state.reindex (S := S) basis).block value.1)).matrix row column =
    (ZMeasurement.branch original value.2 (state.block value.1)).matrix
      (basis.symm row) (basis.symm column)
  simp only [ZMeasurement.branch_matrix, reads, reindex_block_entry]

end ExecutionState

namespace Execution

private theorem reference_prepare {C : Type} [Fintype C]
    {ctx : RuntimeCtx .quantum} {Reference Other : Register} {count : Nat}
    (state : ExecutionState C (ctx.register.prod Reference))
    (basis : Reference.Index ≃ Other.Index) (key : StorageKey)
    (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register) :
    prepareContext (state.reindex (S := ctx.register.prod Other)
        ((Equiv.refl ctx.register.Index).prodCongr basis))
        key layout fresh disjoint prepared =
      (prepareContext state key layout fresh disjoint prepared).reindex
        (S := (ctx.addOwnedLayout key layout fresh disjoint).register.prod Other)
        ((Equiv.refl (ctx.addOwnedLayout key layout fresh disjoint).register.Index).prodCongr
          basis) := by
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  obtain ⟨⟨newRow, oldRow⟩, rowEquation⟩ :=
    (preparedLocalBasisEquiv ctx key layout fresh disjoint).surjective row.1
  obtain ⟨⟨newColumn, oldColumn⟩, columnEquation⟩ :=
    (preparedLocalBasisEquiv ctx key layout fresh disjoint).surjective column.1
  have leftEntry := prepareContext_joined_entry
    (state.reindex (S := ctx.register.prod Other) ((Equiv.refl ctx.register.Index).prodCongr basis))
    key layout fresh disjoint prepared value newRow newColumn
    (oldRow, row.2) (oldColumn, column.2)
  have rightEntry := prepareContext_joined_entry state key layout fresh disjoint prepared
    value newRow newColumn (oldRow, basis.symm row.2) (oldColumn, basis.symm column.2)
  simp only [prepareContextBasisEquiv_pair, rowEquation, columnEquation,
    ExecutionState.reindex_block_entry] at leftEntry rightEntry ⊢
  exact leftEntry.trans rightEntry.symm

namespace State

private theorem reference_history {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference Other : Register} {H K : Type} [Fintype H] [Fintype K]
    (state : State ctx Reference H) (basis : Reference.Index ≃ Other.Index) (update : H → K) :
    State.mapHistory (ctx := ctx) (Reference := Other)
        (state.reindex (S := ctx.register.prod Other)
          ((Equiv.refl ctx.register.Index).prodCongr basis)) update =
      (state.mapHistory update).reindex (S := ctx.register.prod Other)
        ((Equiv.refl ctx.register.Index).prodCongr basis) :=
  ExecutionState.coordinate_reindex_mapClassical state _ _

private theorem reference_pushWorkspace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference Other : Register} {H : Type} [Fintype H]
    (state : State ctx Reference H) (basis : Reference.Index ≃ Other.Index)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    State.pushWorkspace
        (state.reindex (S := ctx.register.prod Other)
          ((Equiv.refl ctx.register.Index).prodCongr basis)) key shape fresh =
      (state.pushWorkspace key shape fresh).reindex
        (S := (ctx.addWorkspace key shape fresh).register.prod Other)
        ((Equiv.refl (ctx.addWorkspace key shape fresh).register.Index).prodCongr basis) := by
  unfold pushWorkspace
  exact ExecutionState.reference_map (R := ctx.register.prod Reference)
    (S := ctx.register.prod Other) _ _ state
    ((Equiv.refl ctx.register.Index).prodCongr basis) _

private theorem reference_popWorkspace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference Other : Register} {H : Type} [Fintype H]
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (state : State (ctx.addWorkspace key shape fresh) Reference H)
    (basis : Reference.Index ≃ Other.Index) :
    State.popWorkspace key shape fresh
        (state.reindex (S := (ctx.addWorkspace key shape fresh).register.prod Other)
          ((Equiv.refl (ctx.addWorkspace key shape fresh).register.Index).prodCongr basis)) =
      (State.popWorkspace key shape fresh state).reindex (S := ctx.register.prod Other)
        ((Equiv.refl ctx.register.Index).prodCongr basis) := by
  unfold popWorkspace
  exact ExecutionState.reference_map (R := ctx.register.prod Reference)
    (S := ctx.register.prod Other) _ _ state
    ((Equiv.refl ctx.register.Index).prodCongr basis) _

end State
end Execution

namespace Circuit

private theorem reference_branch {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {shape : CShape} (input : CInputRef pre shape) (body : shape.Value → Circuit model pre post)
    {Reference Other : Register} (basis : Reference.Index ≃ Other.Index)
    (natural : ∀ value {H : Type} [Fintype H] (state : State pre Reference (model.HiddenState × H)),
      (body value).execute Other
          (state.reindex (S := pre.register.prod Other)
        ((Equiv.refl pre.register.Index).prodCongr basis)) =
        ((body value).execute Reference state).reindex (S := post.register.prod Other)
          ((Equiv.refl post.register.Index).prodCongr basis))
    {H : Type} [Fintype H] (state : State pre Reference (model.HiddenState × H)) :
    (Circuit.branch input body).execute Other
        (state.reindex (S := pre.register.prod Other)
        ((Equiv.refl pre.register.Index).prodCongr basis)) =
      ((Circuit.branch input body).execute Reference state).reindex (S := post.register.prod Other)
        ((Equiv.refl post.register.Index).prodCongr basis) := by
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  rw [execute_branch_block_matrix, ExecutionState.reindex_block_entry,
    execute_branch_block_matrix]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro selected _
  rw [ExecutionState.reference_select, natural, State.reference_history]
  rfl

private theorem reference_iterate {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    (body : Circuit model ctx ctx) {Reference Other : Register}
    (basis : Reference.Index ≃ Other.Index)
    (natural : ∀ {H : Type} [Fintype H] (state : State ctx Reference (model.HiddenState × H)),
      body.execute Other (state.reindex (S := ctx.register.prod Other)
        ((Equiv.refl ctx.register.Index).prodCongr basis)) =
        (body.execute Reference state).reindex (S := ctx.register.prod Other)
          ((Equiv.refl ctx.register.Index).prodCongr basis))
    (count : Nat) {H : Type} [Fintype H] (state : State ctx Reference (model.HiddenState × H)) :
    (Circuit.iterate count body).execute Other
        (state.reindex (S := ctx.register.prod Other)
        ((Equiv.refl ctx.register.Index).prodCongr basis)) =
      ((Circuit.iterate count body).execute Reference state).reindex (S := ctx.register.prod Other)
        ((Equiv.refl ctx.register.Index).prodCongr basis) := by
  induction count generalizing H with
  | zero => rw [execute_iterate_zero, execute_iterate_zero, State.reference_history]
  | succ count induction =>
      rw [execute_iterate_succ, natural, induction,
        State.reference_history, execute_iterate_succ]

/-- Actual execution commutes with an arbitrary change of external-reference basis. -/
theorem execute_referenceReindex {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) {Reference Other : Register}
    (basis : Reference.Index ≃ Other.Index) {H : Type} [Fintype H]
    (state : State pre Reference (model.HiddenState × H)) :
    code.execute Other (state.reindex (S := pre.register.prod Other)
        ((Equiv.refl pre.register.Index).prodCongr basis)) =
      (code.execute Reference state).reindex (S := post.register.prod Other)
        ((Equiv.refl post.register.Index).prodCongr basis) := by
  induction code generalizing H with
  | id ctx =>
      rw [execute_id, execute_id]
      exact ExecutionState.reference_map _ _ _ _ _
  | classical application =>
      rw [execute_classical, execute_classical, ExecutionState.reference_kernel]
      exact ExecutionState.reference_map _ _ _ _ _
  | classicalQuery application =>
      dsimp only [execute, interpret, queryStep]
      rw [ExecutionState.reference_kernel]
      exact ExecutionState.reference_map _ _ _ _ _
  | unitary program =>
      rw [execute_unitary, execute_unitary, ExecutionState.reference_unitary]
      exact ExecutionState.reference_map _ _ _ _ _
  | @measureZ gates oracles ctx operations services wire output =>
      rw [execute_measureZ, execute_measureZ]
      erw [ExecutionState.reference_measure (S := ctx.register.prod Other) state
        ((Equiv.refl ctx.register.Index).prodCongr basis) (fun value => value.1 wire)
        (fun value : (ctx.register.prod Other).Index => value.1 wire) (fun _ => rfl)]
      exact ExecutionState.reference_map _ _ _ _ _
  | retain ctx key shape fresh =>
      rw [execute_retain, execute_retain]
      exact ExecutionState.reference_map _ _ _ _ _
  | prepareZero ctx key layout fresh disjoint =>
      rw [execute_prepareZero, execute_prepareZero]
      dsimp only [State.prepare, State.mapHistory]
      rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance),
        ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
      rw [Execution.reference_prepare]
      exact ExecutionState.reference_map _ _ _ _ _
  | seq first second firstEquation secondEquation =>
      rw [execute_seq, firstEquation, secondEquation, State.reference_history, execute_seq]
  | branch input body bodyEquation =>
      exact reference_branch input body basis (fun value {_} _ original =>
        bodyEquation value original) state
  | iterate count body bodyEquation =>
      exact reference_iterate body basis (fun {_} _ original => bodyEquation original) count state
  | workspace ctx key shape fresh body bodyEquation =>
      change State.popWorkspace key shape fresh
          (body.execute Other (State.pushWorkspace
            (state.reindex (S := ctx.register.prod Other)
              ((Equiv.refl ctx.register.Index).prodCongr basis)) key shape fresh)) =
        (State.popWorkspace key shape fresh
          (body.execute Reference (state.pushWorkspace key shape fresh))).reindex
            (S := ctx.register.prod Other) ((Equiv.refl ctx.register.Index).prodCongr basis)
      rw [State.reference_pushWorkspace, bodyEquation, State.reference_popWorkspace]

end Circuit
end
end QuantumAlg
