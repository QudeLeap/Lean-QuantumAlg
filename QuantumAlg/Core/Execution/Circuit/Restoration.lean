/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Owned.CircuitRestoration

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

private theorem transported_history {kind : ProblemKind} {pre post : RuntimeCtx kind}
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
theorem borrowedRestored_branch {kind : ProblemKind} {pre post : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef pre shape) (body : shape.Value → Circuit pre post)
    (Reference : Register)
    (restores : ∀ value {History : Type} [Fintype History] (state : State pre Reference History),
      (body value).BorrowedRestored Reference state ((body value).execute Reference state))
    {History : Type} [Fintype History] (state : State pre Reference History) :
    (Circuit.branch input body).BorrowedRestored Reference state
      ((Circuit.branch input body).execute Reference state) := by
  let selected := state.selectClassical (fun entry => entry.1.read input)
  let family : shape.Value → State post Reference (History × (Circuit.branch input body).Path) :=
    fun value => ((body value).execute Reference (selected value)).mapHistory
      (fun history => (history.1, ⟨value, history.2⟩))
  have total : ∑ value, (family value).mass ≤ 1 := by
    simp only [family, State.mapHistory_mass, execute_mass]
    exact state.sum_selectClassical_mass_le_one (fun entry => entry.1.read input)
  have actual : (Circuit.branch input body).execute Reference state =
      ExecutionState.finiteSum family total := by
    apply ExecutionState.ext
    intro result
    apply DensityOperator.ext
    exact execute_branch_block_matrix input body state result
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
      ((body value).execute Reference (selected value))
      (fun history => (history.1, (⟨value, history.2⟩ : (Circuit.branch input body).Path)))
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

/-- Actual owned-system execution restores all borrowed classical-reference correlations. -/
theorem borrowedRestored_of_noBorrowedQuantum {kind : ProblemKind}
    {pre post : RuntimeCtx kind} (code : Circuit pre post) :
    ∀ (_noBorrowedQuantum : pre.borrowedQuantumWires = []) (Reference : Register)
      {History : Type} [Fintype History] (state : State pre Reference History),
      code.BorrowedRestored Reference state (code.execute Reference state) := by
  induction code with
  | id =>
      intro _ Reference History _ state
      rw [BorrowedRestored, observeBorrowedAfter_sameContext, execute_id]
      exact observeBorrowed_mapHistory state _
  | classical op =>
      intro _ Reference History _ state
      exact borrowedRestored_classical op state
  | declaredCall call =>
      intro _ Reference History _ state
      exact borrowedRestored_declaredCall call state
  | unitary program placed =>
      intro noBorrowedQuantum Reference History _ state
      exact borrowedRestored_unitary_classicalReference noBorrowedQuantum program placed state
  | measureZ wire output =>
      intro noBorrowedQuantum Reference History _ state
      exact borrowedRestored_measureZ_classicalReference noBorrowedQuantum ⟨wire, output⟩ state
  | randomBits width output =>
      intro _ Reference History _ state
      exact borrowedRestored_randomBits width output state
  | retain ctx key shape fresh =>
      intro _ Reference History _ state
      exact borrowedRestored_retain key shape fresh state
  | prepare ctx key layout fresh disjoint preparation =>
      intro _ Reference History _ state
      exact borrowedRestored_prepare state key layout fresh disjoint preparation
  | seq first second firstIH secondIH =>
      intro noBorrowedQuantum Reference History _ state
      exact borrowedRestored_seq first second state
        (firstIH noBorrowedQuantum Reference state)
        (secondIH (first.borrowedQuantumWires_preserved.trans noBorrowedQuantum) Reference _)
  | branch input body bodyIH =>
      intro noBorrowedQuantum Reference History _ state
      exact borrowedRestored_branch input body Reference
        (fun value {_} _ initial => bodyIH value noBorrowedQuantum Reference initial) state
  | iterate count body bodyIH =>
      intro noBorrowedQuantum Reference History _ state
      exact borrowedRestored_iterate body Reference
        (fun {_} _ initial => bodyIH noBorrowedQuantum Reference initial) count state
  | workspace ctx key shape fresh body bodyIH =>
      intro noBorrowedQuantum Reference History _ state
      exact borrowedRestored_workspace key shape fresh body Reference
        (fun {_} _ initial => bodyIH
          ((ctx.borrowedQuantumWires_addWorkspace key shape fresh).trans noBorrowedQuantum)
          Reference initial) state

end

end QuantumAlg.Circuit
