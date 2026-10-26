/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Owned.CircuitRestoration
import all QuantumAlg.Core.Execution.Borrowed.Parallel
import all QuantumAlg.Core.Execution.Borrowed.OwnedLayoutView
import all QuantumAlg.Core.Execution.Context.OwnedLayoutView.Borrowed

/-!
# Complete borrowed restoration for actual circuits on owned quantum systems

Classical dispatch is the actual finite sum of the selected input fibers.
Restoration in each selected fiber therefore restores the entire original
borrowed classical-quantum-reference state. This composes the actual syntax,
including preparation, finite iteration and lexical workspace. Local quantum
steps require only that the input layout contains no borrowed quantum wires;
all borrowed classical correlations with the external reference remain intact.
-/

namespace QuantumAlg.Circuit

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma transported_history {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (Reference : Register) (sameShape : post.borrowedClassicalShape = pre.borrowedClassicalShape)
    (sameRegister : post.borrowedQuantumLayout.register = pre.borrowedQuantumLayout.register)
    {History Next : Type} [Fintype History] [Fintype Next]
    (state : State post Reference History) (update : History → Next) :
    transportBorrowed Reference sameShape sameRegister
        (observeBorrowed Reference (state.mapHistory update)) =
      transportBorrowed Reference sameShape sameRegister (observeBorrowed Reference state) :=
  congrArg (transportBorrowed Reference sameShape sameRegister)
    (observeBorrowed_mapHistory state update)

/-- Actual stored-value dispatch restores the entire borrowed interface of its selected fibers. -/
lemma borrowedRestored_branch {model : ExecutionModel}
    (environment : model.Environment) {pre post : RuntimeCtx model.kind}
    {allowAllocation : Bool} {shape : CShape} (input : CInputRef pre shape)
    (body : shape.Value → Circuit model pre post allowAllocation)
    (Reference : Register)
    (restores : ∀ value {History : Type} [Fintype History]
      (state : State pre Reference (model.HiddenState × History)),
      (body value).BorrowedRestored Reference state
        ((body value).execute environment Reference state))
    {History : Type} [Fintype History]
      (state : State pre Reference (model.HiddenState × History)) :
    (Circuit.branch input body).BorrowedRestored Reference state
      ((Circuit.branch input body).execute environment Reference state) := by
  let selected := state.selectClassical (fun entry => entry.1.read input)
  let family : shape.Value → State post Reference
      (model.HiddenState × (History × (Circuit.branch input body).Path)) :=
    fun value => ((body value).execute environment Reference (selected value)).mapHistory
      (fun history => (history.1, (history.2.1, ⟨value, history.2.2⟩)))
  have total : ∑ value, (family value).mass ≤ 1 := by
    simp only [family, State.mapHistory_mass, execute_mass]
    exact state.sum_selectClassical_mass_le_one (fun entry => entry.1.read input)
  have actual : (Circuit.branch input body).execute environment Reference state =
      ExecutionState.finiteSum family total := by
    apply ExecutionState.ext
    intro result
    apply DensityOperator.ext
    exact execute_branch_block_matrix environment input body state result
  have selectedTotal : ∑ value, (selected value).mass ≤ 1 :=
    state.sum_selectClassical_mass_le_one (fun entry => entry.1.read input)
  have each : ∀ value,
      transportBorrowed Reference (Circuit.branch input body).borrowedClassicalShape_preserved
          (Circuit.branch input body).borrowedRegister_preserved
          (observeBorrowed Reference (family value)) =
        observeBorrowed Reference (selected value) := by
    intro value
    have mapped := transported_history Reference
      (Circuit.branch input body).borrowedClassicalShape_preserved
      (Circuit.branch input body).borrowedRegister_preserved
      ((body value).execute environment Reference (selected value))
      (fun history => (history.1, (history.2.1,
        (⟨value, history.2.2⟩ : (Circuit.branch input body).Path))))
    exact mapped.trans (restores value (selected value))
  rw [BorrowedRestored, observeBorrowedAfter, actual, observeBorrowed_finiteSum,
    transportBorrowed_finiteSum]
  calc
    _ = ExecutionState.finiteSum (fun value => observeBorrowed Reference (selected value))
        (by simpa only [observeBorrowed_mass] using selectedTotal) := by
      apply ExecutionState.ext
      intro value
      apply DensityOperator.ext
      simp only [ExecutionState.finiteSum_block_matrix, each]
    _ = observeBorrowed Reference (ExecutionState.finiteSum selected selectedTotal) :=
      (observeBorrowed_finiteSum selected selectedTotal).symm
    _ = observeBorrowed Reference state :=
      congrArg (observeBorrowed Reference)
        (ExecutionState.finiteSum_selectClassical state (fun entry => entry.1.read input))

private lemma embedding_noBorrowedQuantum {kind : ProblemKind}
    {localCtx caller : RuntimeCtx kind} (placement : ContextEmbedding localCtx caller)
    (noBorrowedQuantum : caller.borrowedQuantumWires = []) :
    localCtx.borrowedQuantumWires = [] := by
  have permuted := placement.contextEmbedding_borrowedQuantumWires_perm
  rw [noBorrowedQuantum] at permuted
  exact List.map_eq_nil_iff.mp (List.append_eq_nil_iff.mp permuted.eq_nil).1

/-- Actual owned-system execution restores all borrowed classical-reference correlations. -/
lemma borrowedRestored_of_noBorrowedQuantum {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {allowAllocation : Bool}
    (code : Circuit model pre post allowAllocation) (environment : model.Environment) :
    ∀ (_noBorrowedQuantum : pre.borrowedQuantumWires = []) (Reference : Register)
      {History : Type} [Fintype History]
      (state : State pre Reference (model.HiddenState × History)),
      code.BorrowedRestored Reference state (code.execute environment Reference state) := by
  induction code with
  | id ctx =>
      intro _ Reference History _ state
      exact borrowedRestored_id (environment := environment) (ctx := ctx)
        (Reference := Reference) (H := History) state
  | classical op =>
      intro _ Reference History _ state
      exact borrowedRestored_classical (environment := environment) op state
  | classicalQuery application =>
      intro _ Reference History _ state
      exact borrowedRestored_classicalQuery (environment := environment) application state
  | unitary program =>
      intro noBorrowedQuantum Reference History _ state
      exact borrowedRestored_unitary_classicalReference
        (environment := environment) noBorrowedQuantum program state
  | measureZ wire output =>
      intro noBorrowedQuantum Reference History _ state
      exact borrowedRestored_measureZ_classicalReference
        (environment := environment) noBorrowedQuantum ⟨wire, output⟩ state
  | retain ctx key shape fresh =>
      intro _ Reference History _ state
      exact borrowedRestored_retain (environment := environment) key shape fresh state
  | prepareZero ctx key layout fresh disjoint =>
      intro _ Reference History _ state
      exact borrowedRestored_prepareZero
        (environment := environment) state key layout fresh disjoint
  | seq first second firstIH secondIH =>
      intro noBorrowedQuantum Reference History _ state
      exact borrowedRestored_seq (environment := environment) first second state
        (firstIH environment noBorrowedQuantum Reference state)
        (secondIH environment (first.borrowedQuantumWires_preserved.trans
          noBorrowedQuantum) Reference _)
  | branch input body bodyIH =>
      intro noBorrowedQuantum Reference History _ state
      exact borrowedRestored_branch (environment := environment) input body Reference
        (fun value {_} _ initial => bodyIH value environment
          noBorrowedQuantum Reference initial) state
  | iterate count body bodyIH =>
      intro noBorrowedQuantum Reference History _ state
      exact borrowedRestored_iterate (environment := environment) body Reference
        (fun {_} _ initial => bodyIH environment noBorrowedQuantum Reference initial) count state
  | workspace ctx key shape fresh body bodyIH =>
      intro noBorrowedQuantum Reference History _ state
      exact borrowedRestored_workspace (environment := environment) key shape fresh body Reference
        (fun {_} _ initial => bodyIH environment
          ((ctx.borrowedQuantumWires_addWorkspace key shape fresh).trans noBorrowedQuantum)
          Reference initial) state
  | embed placement body bodyIH =>
      intro noBorrowedQuantum Reference History _ state
      exact borrowedRestored_embed (environment := environment) placement body
        (fun ref {_} _ initial => bodyIH environment
          (embedding_noBorrowedQuantum placement noBorrowedQuantum) ref initial)
        Reference state
  | ownedLayoutView view body bodyIH =>
      intro noBorrowedQuantum Reference History _ state
      exact borrowedRestored_ownedLayoutView view body environment Reference state
        (bodyIH environment (view.borrowedQuantumWires_eq.symm.trans noBorrowedQuantum)
          Reference (view.split state))
  | parallelClassical join separate first second firstIH secondIH =>
      intro noBorrowedQuantum Reference History _ state
      exact borrowedRestored_parallelClassical
        (environment := environment) join separate first second
        (fun ref {_} _ initial => firstIH
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩
          (embedding_noBorrowedQuantum
            (ContextEmbedding.alongUnion _ _ separate) noBorrowedQuantum) ref initial)
        (fun ref {_} _ initial => secondIH
          ⟨environment.quantum, join.interpretationRight environment.classical⟩
          (embedding_noBorrowedQuantum
            (ContextEmbedding.alongUnionRight _ _ separate) noBorrowedQuantum) ref initial)
        Reference state
  | parallelQuantum join separate first second firstIH secondIH =>
      intro noBorrowedQuantum Reference History _ state
      exact borrowedRestored_parallelQuantum (environment := environment) join separate first second
        (fun ref {_} _ initial => firstIH
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩
          (embedding_noBorrowedQuantum
            (ContextEmbedding.alongUnion _ _ separate) noBorrowedQuantum) ref initial)
        (fun ref {_} _ initial => secondIH
          ⟨environment.quantum, join.interpretationRight environment.classical⟩
          (embedding_noBorrowedQuantum
            (ContextEmbedding.alongUnionRight _ _ separate) noBorrowedQuantum) ref initial)
        Reference state

end

end QuantumAlg.Circuit
