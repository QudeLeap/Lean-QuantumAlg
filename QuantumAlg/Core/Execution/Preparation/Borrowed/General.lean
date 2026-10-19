/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Preparation.Borrowed.Coordinates
import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.State

/-!
# Fresh preparation preserves the complete borrowed CQ-reference state

Each original classical block retains its entire old quantum-reference
matrix after summing only the newly prepared coordinates. The actual typed
store extension preserves every borrowed classical read. Combining these
two facts preserves the joint borrowed classical, quantum and reference
observation, including arbitrary correlations between its three parts.

Fresh systems remain owned and live. This proof neither releases storage
nor assumes that any original subsystem is pure or independent.
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {count : Nat} {ctx : RuntimeCtx .quantum} {Reference : Register}
  {C D : Type} [Fintype C] [Fintype D]

/-- Grouping actual classical blocks commutes with their fixed fresh preparation. -/
lemma prepareContext_mapClassical
    (state : ExecutionState C (Register.prod ctx.register Reference))
    (key : StorageKey) (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register) (update : C → D) :
    (prepareContext state key layout fresh disjoint prepared).mapClassical update =
      prepareContext (state.mapClassical update) key layout fresh disjoint prepared := by
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  obtain ⟨⟨newRow, oldRow⟩, rfl⟩ :=
    (prepareContextBasisEquiv ctx Reference key layout fresh disjoint).surjective row
  obtain ⟨⟨newColumn, oldColumn⟩, rfl⟩ :=
    (prepareContextBasisEquiv ctx Reference key layout fresh disjoint).surjective column
  rw [prepareContext_joined_entry]
  simp only [ExecutionState.mapClassical, Matrix.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro label _
  by_cases matching : update label = value
  · simp only [matching, if_true]
    exact prepareContext_joined_entry state key layout fresh disjoint prepared label
      newRow newColumn oldRow oldColumn
  · simp only [matching, if_false, Matrix.zero_apply, mul_zero]

omit [Fintype D] in
/-- Every original classical block keeps its complete borrowed-reference observation. -/
lemma prepareContext_borrowed_block
    (state : ExecutionState C (Register.prod ctx.register Reference))
    (key : StorageKey) (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register) (value : C) :
    (ctx.addOwnedLayout key layout fresh disjoint).observeBorrowedWithReference Reference
        ((prepareContext state key layout fresh disjoint prepared).block value) =
      ctx.observeBorrowedWithReference Reference (state.block value) := by
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨borrowedRow, refRow⟩
  rcases column with ⟨borrowedColumn, refColumn⟩
  rw [RuntimeCtx.observeBorrowedWithReference_entry,
    RuntimeCtx.observeBorrowedWithReference_entry]
  let oldRow (complement : ctx.quantumLayout.ComplementBasis ctx.borrowedSelection) :=
    (ctx.quantumLayout.joinSelectedBasis ctx.borrowedSelection
      (ctx.borrowedBasisEquiv.symm borrowedRow) complement, refRow)
  let oldColumn (complement : ctx.quantumLayout.ComplementBasis ctx.borrowedSelection) :=
    (ctx.quantumLayout.joinSelectedBasis ctx.borrowedSelection
      (ctx.borrowedBasisEquiv.symm borrowedColumn) complement, refColumn)
  calc
    _ = ∑ pair : layout.Basis × ctx.quantumLayout.ComplementBasis ctx.borrowedSelection,
        ((prepareContext state key layout fresh disjoint prepared).block value).matrix
          ((ctx.addOwnedLayout key layout fresh disjoint).quantumLayout.joinSelectedBasis
            (ctx.addOwnedLayout key layout fresh disjoint).borrowedSelection
            ((ctx.addOwnedLayout key layout fresh disjoint).borrowedBasisEquiv.symm borrowedRow)
            (PreparationBorrowed.complementBasisEquiv ctx key layout fresh disjoint pair), refRow)
          ((ctx.addOwnedLayout key layout fresh disjoint).quantumLayout.joinSelectedBasis
            (ctx.addOwnedLayout key layout fresh disjoint).borrowedSelection
            ((ctx.addOwnedLayout key layout fresh disjoint).borrowedBasisEquiv.symm borrowedColumn)
            (PreparationBorrowed.complementBasisEquiv ctx key layout fresh disjoint pair),
              refColumn) :=
      ((PreparationBorrowed.complementBasisEquiv ctx key layout fresh disjoint).sum_comp _).symm
    _ = ∑ complement : ctx.quantumLayout.ComplementBasis ctx.borrowedSelection,
        ∑ newBasis : layout.Basis,
        ((prepareContext state key layout fresh disjoint prepared).block value).matrix
          (prepareContextBasisEquiv ctx Reference key layout fresh disjoint
            (newBasis, oldRow complement))
          (prepareContextBasisEquiv ctx Reference key layout fresh disjoint
            (newBasis, oldColumn complement)) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro complement _
      apply Finset.sum_congr rfl
      intro newBasis _
      exact congrArg₂
        (fun left right : (Register.prod
          (ctx.addOwnedLayout key layout fresh disjoint).register Reference).Index =>
          ((prepareContext state key layout fresh disjoint prepared).block value).matrix
            left right)
        (congrArg (fun basis => (basis, refRow))
          (PreparationBorrowed.join_prepared ctx key layout fresh disjoint
            borrowedRow newBasis complement))
        (congrArg (fun basis => (basis, refColumn))
          (PreparationBorrowed.join_prepared ctx key layout fresh disjoint
            borrowedColumn newBasis complement))
    _ = _ := Finset.sum_congr rfl fun complement _ =>
      prepareContext_old_block_marginal state key layout fresh disjoint prepared value
        (oldRow complement) (oldColumn complement)

end

end QuantumAlg.Execution

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Fresh owned preparation restores every borrowed classical-quantum-reference correlation. -/
lemma borrowedRestored_prepareZero {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    (environment :
      (ExecutionModel.quantum gates oracles operations classicalOracles).Environment)
    {ctx : RuntimeCtx .quantum} {Reference : Register}
    {H : Type} [Fintype H] (state : State ctx Reference (classicalOracles.HiddenState × H))
    (key : StorageKey) {count : Nat} (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (Circuit.prepareZero (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles)
      ctx key layout fresh disjoint).BorrowedRestored Reference state
      ((Circuit.prepareZero (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles)
        ctx key layout fresh disjoint).execute environment Reference state) := by
  change observeBorrowed Reference
    ((state.prepare key layout fresh disjoint (BasisPreparation.zero layout)).mapHistory
      (fun record => (record.1.1, (record.1.2, record.2)))) =
    observeBorrowed Reference state
  apply ExecutionState.ext
  intro value
  rw [observeBorrowed_block, observeBorrowed_block]
  simp only [State.prepare, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def,
    Store.readBorrowedClassical_pushOwnedLayout]
  rw [prepareContext_mapClassical]
  exact prepareContext_borrowed_block
    (state.mapClassical fun label => label.1.readBorrowedClassical)
    key layout fresh disjoint (BasisPreparation.zero layout).normalized value

end

end QuantumAlg.Circuit
