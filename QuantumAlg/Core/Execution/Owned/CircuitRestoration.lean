/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Borrowed.Classical.Reference
import all QuantumAlg.Core.Execution.Preparation.Borrowed.General
import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Core.Execution.Classical.Iteration

/-!
# Compositional restoration for circuits acting on owned quantum systems

The complete borrowed classical and quantum interface is observed jointly
with an arbitrary external reference. The actual interpreter's finite
branches, iteration and lexical workspace compose this same observation;
none of these laws substitutes separate marginals or assumes independent
stored classical inputs. Local quantum instructions will use the actual
absence of borrowed quantum wires, preserved by the instruction language.
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace Execution

/-- The joint borrowed observation is linear over the actual finite sum of state blocks. -/
lemma observeBorrowed_finiteSum {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {History Index : Type} [Fintype History] [Fintype Index]
    (states : Index → State ctx Reference History) (total : ∑ index, (states index).mass ≤ 1) :
    observeBorrowed Reference (ExecutionState.finiteSum states total) =
      ExecutionState.finiteSum (fun index => observeBorrowed Reference (states index))
        (by simpa only [observeBorrowed_mass] using total) := by
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨row, refRow⟩
  rcases column with ⟨column, refColumn⟩
  rw [ExecutionState.finiteSum_block_matrix]
  simp only [Matrix.sum_apply, observeBorrowed_entry,
    ExecutionState.finiteSum_block_matrix]
  calc
    _ = ∑ complement, ∑ label, ∑ index,
        if label.1.readBorrowedClassical = value then
          ((states index).block label).matrix
            (ctx.quantumLayout.joinSelectedBasis ctx.borrowedSelection
              (ctx.borrowedBasisEquiv.symm row) complement, refRow)
            (ctx.quantumLayout.joinSelectedBasis ctx.borrowedSelection
              (ctx.borrowedBasisEquiv.symm column) complement, refColumn)
        else 0 := by
      apply Finset.sum_congr rfl
      intro complement _
      apply Finset.sum_congr rfl
      intro label _
      by_cases same : label.1.readBorrowedClassical = value
      · simp only [if_pos same]
      · simp only [if_neg same, Finset.sum_const_zero]
    _ = ∑ complement, ∑ index, ∑ label,
        if label.1.readBorrowedClassical = value then
          ((states index).block label).matrix
            (ctx.quantumLayout.joinSelectedBasis ctx.borrowedSelection
              (ctx.borrowedBasisEquiv.symm row) complement, refRow)
            (ctx.quantumLayout.joinSelectedBasis ctx.borrowedSelection
              (ctx.borrowedBasisEquiv.symm column) complement, refColumn)
        else 0 := by
      apply Finset.sum_congr rfl
      intro complement _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Equality transport commutes with that same finite family of complete borrowed blocks. -/
lemma transportBorrowed_finiteSum
    {sourceShape targetShape : CShape} {sourceRegister targetRegister : Register}
    (Reference : Register) (sameShape : sourceShape = targetShape)
    (sameRegister : sourceRegister = targetRegister) {Index : Type} [Fintype Index]
    (states : Index → ExecutionState sourceShape.Value (Register.prod sourceRegister Reference))
    (total : ∑ index, (states index).mass ≤ 1) :
    transportBorrowed Reference sameShape sameRegister (ExecutionState.finiteSum states total) =
      ExecutionState.finiteSum
        (fun index => transportBorrowed Reference sameShape sameRegister (states index))
        (by simpa only [transportBorrowed_mass] using total) := by
  cases sameShape
  cases sameRegister
  rfl

/-- Entering real lexical workspace preserves the complete original borrowed observation. -/
lemma observeBorrowed_pushWorkspace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    observeBorrowed Reference (state.pushWorkspace key shape fresh) =
      observeBorrowed Reference state := by
  let newRead : Store (ctx.addWorkspace key shape fresh) × History →
      ctx.borrowedClassicalShape.Value := fun entry => entry.1.readBorrowedClassical
  let push : Store ctx × History → Store (ctx.addWorkspace key shape fresh) × History :=
    fun entry => (entry.1.pushWorkspace key shape fresh, entry.2)
  have mapped := congrArg
    (fun result : ExecutionState (Store (ctx.addWorkspace key shape fresh) × History)
        (Register.prod ctx.register Reference) => result.mapClassical newRead)
    (State.state_pushWorkspace_as_mapClassical key shape fresh Reference state)
  have composed := mapped.trans
    (ExecutionState.executionState_mapClassical_comp state push newRead)
  have reads : newRead ∘ push = fun entry : Store ctx × History =>
      entry.1.readBorrowedClassical := by
    funext entry
    exact Store.readBorrowedClassical_pushWorkspace entry.1 key shape fresh
  rw [reads] at composed
  apply ExecutionState.ext
  intro value
  have density := congrArg
    (fun observed : ExecutionState ctx.borrowedClassicalShape.Value
        (Register.prod ctx.register Reference) =>
      ctx.observeBorrowedWithReference Reference (observed.block value)) composed
  exact (observeBorrowed_block Reference (state.pushWorkspace key shape fresh) value).trans
    (density.trans (observeBorrowed_block Reference state value).symm)

/-- Exiting that lexical head retains all original borrowed classical-reference correlations. -/
lemma observeBorrowed_popWorkspace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {History : Type} [Fintype History]
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (state : State (ctx.addWorkspace key shape fresh) Reference History) :
    observeBorrowed Reference (State.popWorkspace key shape fresh state) =
      observeBorrowed Reference state := by
  let oldRead : Store ctx × History → ctx.borrowedClassicalShape.Value :=
    fun entry => entry.1.readBorrowedClassical
  let pop : Store (ctx.addWorkspace key shape fresh) × History → Store ctx × History :=
    fun entry => (Store.popWorkspace key shape fresh entry.1, entry.2)
  have mapped := congrArg
    (fun result : ExecutionState (Store ctx × History) (Register.prod ctx.register Reference) =>
      result.mapClassical oldRead)
    (State.state_popWorkspace_as_mapClassical key shape fresh Reference state)
  have composed := mapped.trans
    (ExecutionState.executionState_mapClassical_comp
      (R := Register.prod ctx.register Reference) state pop oldRead)
  have reads : oldRead ∘ pop =
      fun entry : Store (ctx.addWorkspace key shape fresh) × History =>
        entry.1.readBorrowedClassical := by
    funext entry
    exact Store.readBorrowedClassical_popWorkspace key shape fresh entry.1
  rw [reads] at composed
  apply ExecutionState.ext
  intro value
  have density := congrArg
    (fun observed : ExecutionState ctx.borrowedClassicalShape.Value
        (Register.prod ctx.register Reference) =>
      ctx.observeBorrowedWithReference Reference (observed.block value)) composed
  exact (observeBorrowed_block Reference (State.popWorkspace key shape fresh state) value).trans
    (density.trans (observeBorrowed_block Reference state value).symm)

end Execution

namespace Circuit

open Execution

/-- Every actual finite iteration restores the same joint interface when its actual body does. -/
lemma borrowedRestored_iterate {model : ExecutionModel}
    (environment : model.Environment) {ctx : RuntimeCtx model.kind}
    {allowAllocation : Bool} (body : Circuit model ctx ctx allowAllocation) (Reference : Register)
    (restores : ∀ {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      body.BorrowedRestored Reference state (body.execute environment Reference state))
    (count : Nat) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.iterate count body).BorrowedRestored Reference state
      ((Circuit.iterate count body).execute environment Reference state) := by
  induction count generalizing History with
  | zero =>
      rw [BorrowedRestored, observeBorrowedAfter_sameContext, execute_iterate_zero]
      exact observeBorrowed_mapHistory state _
  | succ count ih =>
      rw [BorrowedRestored, observeBorrowedAfter_sameContext, execute_iterate_succ,
        observeBorrowed_mapHistory]
      have later := ih (body.execute environment Reference state)
      have first := restores state
      change observeBorrowed Reference
        ((Circuit.iterate count body).execute environment Reference (body.execute environment
          Reference state)) =
          observeBorrowed Reference (body.execute environment Reference state) at later
      change observeBorrowed Reference (body.execute environment Reference state) =
        observeBorrowed Reference state at first
      exact later.trans first

/-- Lexical push, restoring body and pop preserve the complete original borrowed interface. -/
lemma borrowedRestored_workspace {model : ExecutionModel}
    (environment : model.Environment) {ctx : RuntimeCtx model.kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit model (ctx.addWorkspace key shape fresh)
      (ctx.addWorkspace key shape fresh) true)
    (Reference : Register)
    (restores : ∀ {History : Type} [Fintype History]
      (state : State (ctx.addWorkspace key shape fresh) Reference (model.HiddenState × History)),
      body.BorrowedRestored Reference state (body.execute environment Reference state))
    {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.workspace ctx key shape fresh body).BorrowedRestored Reference state
      ((Circuit.workspace ctx key shape fresh body).execute environment Reference state) := by
  rw [BorrowedRestored, observeBorrowedAfter_sameContext, execute_workspace]
  have actual := restores (state.pushWorkspace key shape fresh)
  change observeBorrowed Reference
    (body.execute environment Reference (state.pushWorkspace key shape fresh)) =
      observeBorrowed Reference (state.pushWorkspace key shape fresh) at actual
  exact (observeBorrowed_popWorkspace key shape fresh _).trans
    (actual.trans (observeBorrowed_pushWorkspace state key shape fresh))

end Circuit

end

end QuantumAlg
