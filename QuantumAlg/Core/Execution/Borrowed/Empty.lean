/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Reference.Unitary

/-!
# Reference restoration when the runtime has no borrowed cells or wires

An empty runtime borrowed interface still observes the complete external
reference. The observation is its actual partial trace, not a vacuous state
promise [dW19, qcnotes.tex:5381]. Local unitary execution preserves this
observation by the exact reference matrix equation of its interpreter.
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma emptySelectedBasis_unique {count : Nat} (layout : QuantumLayout count)
    (selection : Finset (Fin count)) (empty : selection = ∅)
    (left right : layout.SelectedBasis selection) : left = right := by
  funext index
  have impossible : index.val ∉ selection := by simp [empty]
  exact (impossible index.property).elim

private def emptyComplementEquiv {count : Nat} (layout : QuantumLayout count)
    (selection : Finset (Fin count)) (empty : selection = ∅)
    (selected : layout.SelectedBasis selection) :
    layout.ComplementBasis selection ≃ layout.Basis where
  toFun complement := layout.joinSelectedBasis selection selected complement
  invFun basis := layout.restrictComplementBasis selection basis
  left_inv complement := congrArg Prod.snd
    (layout.selectionBasisEquiv_join selection selected complement)
  right_inv basis := by
    rw [emptySelectedBasis_unique layout selection empty selected
      (layout.restrictSelectedBasis selection basis)]
    exact layout.joinSelectedBasis_restrict selection basis

private lemma sum_emptyComplement_diagonal {count : Nat} (layout : QuantumLayout count)
    (selection : Finset (Fin count)) (empty : selection = ∅)
    (left right : layout.SelectedBasis selection) (entry : layout.Basis → layout.Basis → ℂ) :
    (∑ complement : layout.ComplementBasis selection,
      entry (layout.joinSelectedBasis selection left complement)
        (layout.joinSelectedBasis selection right complement)) =
      ∑ basis : layout.Basis, entry basis basis := by
  rw [← emptySelectedBasis_unique layout selection empty left right]
  exact (emptyComplementEquiv layout selection empty left).sum_comp (fun basis => entry basis basis)

namespace Execution

/-- A uniquely valued borrowed classical interface and no borrowed quantum wires
still observe the entire external reference marginal. -/
lemma observeBorrowed_empty_entry_of_subsingleton {kind : ProblemKind} {ctx : RuntimeCtx kind}
    [Subsingleton ctx.borrowedClassicalShape.Value]
    (noQuantum : ctx.borrowedQuantumWires = []) {Reference : Register}
    {H : Type} [Fintype H] (state : State ctx Reference H)
    (value : ctx.borrowedClassicalShape.Value)
    (left right : ctx.borrowedQuantumLayout.Basis) (refLeft refRight : Reference.Index) :
    ((observeBorrowed Reference state).block value).matrix (left, refLeft) (right, refRight) =
      ∑ basis : ctx.register.Index, state.quantumMarginal.matrix
        (basis, refLeft) (basis, refRight) := by
  have empty : ctx.borrowedSelection = ∅ := by
    ext index
    simp [RuntimeCtx.mem_borrowedSelection, noQuantum]
  have sameRead (label : Store ctx × H) : label.1.readBorrowedClassical = value :=
    Subsingleton.elim _ _
  rw [observeBorrowed_entry]
  simp only [sameRead, if_true]
  change (∑ complement : ctx.quantumLayout.ComplementBasis ctx.borrowedSelection,
    ∑ label : Store ctx × H,
      (state.block label).matrix
        (ctx.quantumLayout.joinSelectedBasis ctx.borrowedSelection
          (ctx.borrowedBasisEquiv.symm left) complement, refLeft)
        (ctx.quantumLayout.joinSelectedBasis ctx.borrowedSelection
          (ctx.borrowedBasisEquiv.symm right) complement, refRight)) =
    ∑ basis : ctx.register.Index, (∑ label : Store ctx × H, (state.block label).matrix)
      (basis, refLeft) (basis, refRight)
  simp only [Matrix.sum_apply]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun basis label =>
    (state.block label).matrix (basis, refLeft) (basis, refRight))]
  apply Finset.sum_congr rfl
  intro label _
  exact sum_emptyComplement_diagonal ctx.quantumLayout ctx.borrowedSelection empty
    (ctx.borrowedBasisEquiv.symm left) (ctx.borrowedBasisEquiv.symm right)
    (fun a b => (state.block label).matrix (a, refLeft) (b, refRight))

/-- With no borrowed values or wires, the joint observation is the full reference marginal. -/
lemma observeBorrowed_empty_entry {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (noClassical : ctx.borrowedClassicalShape = .unit)
    (noQuantum : ctx.borrowedQuantumWires = []) {Reference : Register}
    {H : Type} [Fintype H] (state : State ctx Reference H)
    (value : ctx.borrowedClassicalShape.Value)
    (left right : ctx.borrowedQuantumLayout.Basis) (refLeft refRight : Reference.Index) :
    ((observeBorrowed Reference state).block value).matrix (left, refLeft) (right, refRight) =
      ∑ basis : ctx.register.Index, state.quantumMarginal.matrix
        (basis, refLeft) (basis, refRight) := by
  let : Subsingleton ctx.borrowedClassicalShape.Value := by
    rw [noClassical]
    exact ⟨fun a b => by cases a; cases b; rfl⟩
  exact observeBorrowed_empty_entry_of_subsingleton noQuantum state value left right
    refLeft refRight

end Execution

namespace Circuit

variable {allowAllocation : Bool}

/-- Local unitary execution restores every uniquely valued borrowed classical
interface together with the external reference when no quantum wire is borrowed. -/
lemma borrowedRestored_unitary_noBorrowedQuantum {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    (environment :
      (ExecutionModel.quantum gates oracles operations classicalOracles).Environment)
    {ctx : RuntimeCtx .quantum}
    [Subsingleton ctx.borrowedClassicalShape.Value]
    (noQuantum : ctx.borrowedQuantumWires = []) {Reference : Register}
    {H : Type} [Fintype H] (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    (state : Execution.State ctx Reference (classicalOracles.HiddenState × H)) :
    (Circuit.unitary (allowAllocation := allowAllocation)
      (operations := operations) (classicalOracles := classicalOracles)
      program).BorrowedRestored Reference state
      ((Circuit.unitary (allowAllocation := allowAllocation)
      (operations := operations) (classicalOracles := classicalOracles)
      program).execute environment Reference state) := by
  rw [BorrowedRestored, Execution.observeBorrowedAfter_sameContext]
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨left, refLeft⟩
  rcases column with ⟨right, refRight⟩
  rw [Execution.observeBorrowed_empty_entry_of_subsingleton noQuantum,
    Execution.observeBorrowed_empty_entry_of_subsingleton noQuantum]
  exact unitary_reference_entry (allowAllocation := allowAllocation)
    environment program state refLeft refRight

/-- Local unitary execution restores an empty borrowed interface together with its reference. -/
lemma borrowedRestored_unitary_noBorrowed {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    (environment :
      (ExecutionModel.quantum gates oracles operations classicalOracles).Environment)
    {ctx : RuntimeCtx .quantum}
    (noClassical : ctx.borrowedClassicalShape = .unit)
    (noQuantum : ctx.borrowedQuantumWires = []) {Reference : Register}
    {H : Type} [Fintype H] (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    (state : Execution.State ctx Reference (classicalOracles.HiddenState × H)) :
    (Circuit.unitary (allowAllocation := allowAllocation)
      (operations := operations) (classicalOracles := classicalOracles)
      program).BorrowedRestored Reference state
      ((Circuit.unitary (allowAllocation := allowAllocation)
      (operations := operations) (classicalOracles := classicalOracles)
      program).execute environment Reference state) := by
  let : Subsingleton ctx.borrowedClassicalShape.Value := by
    rw [noClassical]
    exact ⟨fun a b => by cases a; cases b; rfl⟩
  exact borrowedRestored_unitary_noBorrowedQuantum (allowAllocation := allowAllocation)
    environment noQuantum program state

end Circuit

end

end QuantumAlg
